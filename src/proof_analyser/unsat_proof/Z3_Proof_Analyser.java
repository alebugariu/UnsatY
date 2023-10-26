/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proof_analyser.unsat_proof;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Params;
import com.microsoft.z3.Pattern;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.enumerations.Z3_decl_kind;

import proof_analyser.Input_Reader;
import quant_var.Quant_Var_Handler;
import recovery.Proof_Concrete_Values;
import util.Exception_Handler;
import util.Proof_Exception;
import util.Setup;
import util.Verbal_Output;
import util.Verbal_Output.Log_Type;

/*
 * This class is used to generate and analyze a Z3 unsat-proof and find explicit
 * instantiations of quantified variables in it. Fortunately, these are always
 * marked as Z3_OP_PR_QUANT_INST by the Z3 API and are therefore easy to find.
 * Unfortunately, the Z3 API cannot directly provide us with a list of
 * (quantified variable, concrete value) pairs, so it is our task to find them.
 * 
 * Concrete values can be constants (e.g., 1, true), (user-defined or fresh)
 * free variables and function applications of those.
 * 
 * According to the Z3 API, expressions marked as Z3_OP_PR_QUANT_INST have the
 * form "(or (not (forall (x) (P x))) (P a))", where the quantified variable x
 * is instantiated with the concrete value a. As can be seen, x and a do not
 * necessarily have to occur purely. Instead, they can occur within a formula P.
 * In practice, these quantifier instantiations are often more complex:
 * - There may be multiple quantified variables instantiated within the same
 *   Z3_OP_PR_QUANT_INST expression.
 * - The formula P may consist of a number of nested functions, where we must
 *   first locate the quantified variable and the corresponding concrete value
 *   with which it is instantiated.
 * - There may even be nested Z3_OP_PR_QUANT_INST expressions in P.
 * 
 * This can also be seen in the following concrete example:
 * "(let ((a!1 (forall ((x0 Bool) (y0 Bool)) (! (not (or (not x0) (not y0))) :pattern ((f x0 y0))))))
 * (let ((a!2 (or (not a!1) (not (or (not false) (not false)))))) (quant-inst a!2)))."
 * If we substitute a!1 in the second line with its definition from the first
 * line and remove some of the irrelevant details, we get:
 * "(or (not (forall ((x0 Bool) (y0 Bool)) (not (or (not x0) (not y0))))) (not (or (not false) (not false))))".
 * There are two quantified Boolean variables x0 and y0, both instantiated to
 * false. To find this out automatically, we first have to track x0 (or y0) in
 * the first part of this so-called Or-Not expression, before we can find the
 * corresponding concrete value (false) in the same place in the second part.
 * 
 * Objects of this class should be created by the Proof_Analyser_Framework so 
 * that the arguments of the constructor are set appropriately.
 */

public class Z3_Proof_Analyser implements Proof_Analyser {

	// Takes care of printing results and intermediate steps.
	// Is provided by the Input_Reader in the constructor.
	private Verbal_Output verbal_output;

	// Contains all the information we extracted from the input.
	// Is provided in the constructor.
	private Input_Reader input_reader;

	// "The main interaction with Z3 happens via the Context. It maintains all data
	// structures related to terms and formulas that are created relative to them."
	// - from the Z3 API.
	// Is provided by the Input_Reader in the constructor.
	private Context context;

	// Contains the Z3 unsat-proof for the input_file.
	// Is null before the method prove() has been called.
	private Z3_Unsat_Proof proof;

	// Allows us to store and retrieve information about quantified variables.
	// Is provided by the Input_Reader in the constructor.
	// Will be modified by the methods here. Concretely, we will add further
	// information about quantifier instantiations.
	private Quant_Var_Handler quant_vars;

	// How many quantifier instantiations were performed in the proof
	private int quant_inst;
	// How many quantifier instantiations have been already analyzed
	private int quant_inst_counter;
	private Set<Expr<?>> visited_expressions;

	// Expects the input_reader to be already set up appropriately.
	// Do not call this constructor yourself but use the Proof_Analyser_Framework.
	public Z3_Proof_Analyser(Input_Reader input_reader) {
		this.verbal_output = input_reader.verbal_output;
		this.input_reader = input_reader;
		this.context = input_reader.context;
		this.quant_vars = input_reader.quant_vars;
		if (Setup.log_type == Log_Type.full) {
			verbal_output.add_to_buffer("[INFO]", "Created a Z3_Proof_Analyser object.");
		}
		this.quant_inst_counter = 0;
		this.visited_expressions = new LinkedHashSet<Expr<?>>();
	}

	@Override
	public void generate_unsat_proof() throws Proof_Exception {
		// First, we create a solver and set it up appropriately.
		Solver solver = context.mkSolver();
		Params solver_settings = context.mkParams();
		solver_settings.add("auto-config", false);
		solver_settings.add("mbqi", true);
		solver_settings.add("proof", true);
		solver_settings.add("timeout", Math.min(Setup.timeout, Setup.z3_timout));
		solver_settings.add("max_memory", Setup.z3_memory_limit);
		solver.setParameters(solver_settings);
		// Next, we want to use the solver to check whether the input is unsatisfiable.
		// If that's the case, then we can generate an unsat-proof and look for
		// quantifier instantiations in it. If not, then we throw a Proof_Exception.
		solver.add(input_reader.input);
		Status status = solver.check();
		String input_file = input_reader.get_initial_input_file().getName();

		if (status.equals(Status.SATISFIABLE)) {
			Exception_Handler.throw_proof_exception(
					"Z3 failed to produce an unsat-proof for " + input_file + ", as it is satisfiable.", verbal_output,
					Status.SATISFIABLE);
			return;
		}
		if (status.equals(Status.UNKNOWN)) {
			System.out.println(solver.getStatistics());
			Exception_Handler.throw_proof_exception("Z3 failed to produce an unsat-proof for " + input_file
					+ ", because: " + solver.getReasonUnknown() + ".", verbal_output, Status.UNKNOWN);
			return;
		}

		if (status.equals(Status.UNSATISFIABLE)) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]", "Successfully generated an unsat-proof with Z3.");
			}
			Expr<?> api_proof = solver.getProof();
			proof = new Z3_Unsat_Proof(api_proof);
		}
	}

	// Looks for quantifier instantiations in the generated proof and gives them to
	// quant_vars.
	// Throws a Proof_Exception if Z3 cannot prove unsat within the resources
	// defined in the class Setup.
	// Returns quant_vars.
	@Override
	public Quant_Var_Handler extract_quantifier_instantiations() throws Proof_Exception {

		input_reader.analyze_input();
		Expr<?> proof_expr = proof.getProofExpression();
		quant_inst = proof_expr.toString().split("quant-inst").length - 1;
		find_quantifier_instantiations(proof_expr);
		// Print what we encountered while looking at the unsat-proof.
		if (Setup.log_type == Log_Type.full) {
			verbal_output.print_prove(quant_vars);
		}
		return quant_vars;
	}

	// Recursively looks for quantifier instantiations in the expressions and gives
	// them to quant_vars.
	private void find_quantifier_instantiations(Expr<?> expression) throws Proof_Exception {
		// Quantifier instantiations are marked as Z3_OP_PR_QUANT_INST.
		if (Thread.currentThread().isInterrupted()) {
			throw new Proof_Exception("Interrupted while finding quantifier instantations in the proof (only "
					+ quant_inst_counter + " out of " + quant_inst + " found)");
		}

		if (quant_inst_counter == quant_inst) {
			return;
		}
		visited_expressions.add(expression);
		if (expression.isApp()) {
			// We therefore only care about expressions that are applications of functions,
			// because isProofQuantInst only returns true if so does isApp.
			if (expression.isProofQuantInst()) {
				if (Setup.log_type == Log_Type.full) {
					verbal_output.add_to_buffer("[INFO]", "Found a quantifier instantiation: " + expression + ".");
				}
				quant_inst_counter++;
				// We now want to get the (quantified variable, concrete value) pairs and give
				// them to quant_vars.
				try {
					dive_into_quantifier_instantiation(expression);
				} catch (Proof_Exception e) {
					// The quantifier did not have the expected Or-Not form.
					if (Setup.log_type == Log_Type.full) {
						verbal_output.add_to_buffer("[INFO]", "We therefore skip this quantifer instantiation.");
					}
				}
			}
			// No matter whether the current_expression is marked as Z3_OP_PR_QUANT_INST or
			// not, it may contain an expression marked as Z3_OP_PR_QUANT_INST somewhere in
			// its arguments, which we therefore recursively look at.
			for (Expr<?> arg : expression.getArgs()) {
				if (arg.toString().contains("quant-inst") && !visited_expressions.contains(arg)) {
					find_quantifier_instantiations(arg);
				}
			}
		}
	}

	// Traverses the quantifier_instantiation to find pairs of quantified variables
	// and concrete values to instantiate them with.
	// Assumes that quantifier_instantiation has the so-called Or-Not form:
	// "(or (not (forall (x) (P x)))) (P a))".
	// Throws a Proof_Exception if the quantifier_instantiation does not have the
	// expected Or-Not form.
	private void dive_into_quantifier_instantiation(Expr<?> quantifier_instantiation) throws Proof_Exception {
		// quantifier_instantiation: "(or (not (forall (x) (P x)))) (P a))".
		Expr<?> quantifier_instantiation_or_part = quantifier_instantiation.getArgs()[0];
		// quantifier_instantiation_or_part: "(not (forall (x) (P x)))".
		Expr<?> quantifier_instantiation_not_part = quantifier_instantiation_or_part.getArgs()[0];
		// quantifier_instantiation_not_part: "(not (forall (x) (P x)))".
		Expr<?> quantified_quantifier = quantifier_instantiation_not_part.getArgs()[0];
		// quantified_quantifier: "(forall (x) (P x))".
		Expr<?> instantiated_quantifier = quantifier_instantiation_or_part.getArgs()[1];
		// instantiated_quantifier: "(P a)".
		if (!quantifier_instantiation_or_part.isOr() || !quantifier_instantiation_not_part.isNot()
				|| !quantified_quantifier.isQuantifier()) {
			Exception_Handler.throw_proof_exception("The quantifier instantiation " + quantifier_instantiation
					+ " does not have the expected (or (not (forall (x) (P x))) (P a)) form.", verbal_output);
		}
		if (Setup.log_type == Log_Type.full) {
			verbal_output.add_to_buffer("[INFO]", "The quantifier instantiation has the expected Or-Not form.");
		}
		// Cast quantified_quantifier to a Quantifier so we can use Quantifier methods.
		// This always succeeds because we checked for isQuantifier before.
		Quantifier quantifier = ((Quantifier) quantified_quantifier);
		Symbol[] quantified_variable_names = quantifier.getBoundVariableNames();
		// We need the sort of each quantified variable to make sure that the concrete
		// value we find really fits the quantified variable.
		Sort[] quantified_variable_sorts = quantifier.getBoundVariableSorts();
		// We need the number of quantified variables for De-Bruijn indexing.
		int len = quantified_variable_names.length;
		if (Setup.log_type == Log_Type.full) {
			verbal_output.add_to_buffer("[INFO]", "It instantiates the following quantified variables: "
					+ Arrays.toString(quantified_variable_names) + ".");
		}
		// We now track each of the quantified variables in the quantified_quantifier,
		// before we look for the corresponding concrete value in the same place in the
		// instantiated_quantifier. Note that even if the quantified variable appears
		// multiple times in the body of the Quantifier, it suffices to track it once as
		// each occurrence of it must be instantiated to the same value.
		for (int i = 0; i < quantified_variable_names.length; i++) {
			/*
			 * De-Bruijn Indexing Intermezzo:
			 * 
			 * As explained before, we first track the quantified variable. We therefore
			 * look for the variable within the body of the Quantifier that corresponds to
			 * our quantified variable. This variable is however not directly the quantified
			 * variable (so we cannot check for equality), but some sort of local variable
			 * that references the actual quantified variable by using De-Bruijn indexing.
			 * 
			 * "The De Bruijn index is a natural number that represents an occurrence of a
			 * variable in a lambda-term, and denotes the number of binders that are in
			 * scope between that occurrence and its corresponding binder." - Wikipedia.
			 * 
			 * Since our quantifier is of the form (forall (x0, x1, ...) (P x0, x1, ...)),
			 * we can easily determine the De-Bruijn index for each quantified variable.
			 * Namely, if we have n quantified variables in total, then the i-th of them has
			 * De-Bruijn index n-i-1 (e.g. x0 has index n-1, x1 has index n-2, ...).
			 * 
			 * If there is however a nested Quantifier in the quantified_quantifier, then we
			 * need to be more careful. To overcome this, we just add the number of
			 * quantified variables that the nested Quantifier defines to the current index.
			 */
			// Since our quantified variable may be in a nested expression, we want to track
			// the "path" we take through the expression on our way towards it. We do this
			// by memorizing the index (in the arguments of the current expression) of each
			// sub-expression we "dive" into.
			List<Integer> tracking_indexes = new LinkedList<Integer>();
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]", "Looking for the quantified variable "
						+ quantified_variable_names[i] + " in " + quantifier + ".");
			}
			if (!track_function_applications_until_quantified_variable(len - i - 1, quantifier.getBody(),
					tracking_indexes)) {
				if (Setup.log_type == Log_Type.full) {
					verbal_output.add_to_buffer("[PROBLEM]", "Failed to find the quantified variable "
							+ quantified_variable_names[i] + " in the quantifier instantiation.");
				}
				continue;
			}
			// We then take the very same "path" in the instantiated_quantifier to find the
			// corresponding concrete value, before we give the pair to quant_vars.
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]",
						"Looking for the concrete value corresponding to the quantified variable "
								+ quantified_variable_names[i] + " in " + instantiated_quantifier + ".");
			}
			repeat_function_applications_until_concrete_value(quantified_variable_names[i],
					quantified_variable_sorts[i], instantiated_quantifier, tracking_indexes);
		}
	}

	// Recursively traverses the current_expression until it possibly finds a
	// variable that references the expected_variable_index. Remembers the index of
	// each sub-expression it "dives" into so that once the suitable variable is
	// found, the list tracking_indexes can be used to reconstruct that path.
	// Returns false if no suitable variable is ever found (should not happen).
	private Boolean track_function_applications_until_quantified_variable(int expected_variable_index,
			Expr<?> current_expression, List<Integer> tracking_indexes) {
		if (current_expression.isVar() && current_expression.getIndex() == (expected_variable_index)) {
			// If the current_expression is a variable that references the
			// expected_variable_index, we can return true since tracking_indexes contains
			// all the information we need to reconstruct the path we used to get here.
			return true;
		}
		if (current_expression.isApp()) {
			// If the current_expression is an application, it is definitely no variable but
			// the variable we are looking for may be somewhere in its arguments, which we
			// therefore recursively look at.
			Expr<?>[] sub_expressions = current_expression.getArgs();
			if (current_expression.isQuantifier()) {
				// As already mentioned, we need to update the index according to the number of
				// quantified variables in the nested Quantifier.
				expected_variable_index += ((Quantifier) current_expression).getBoundVariableNames().length;
				sub_expressions = ((Quantifier) current_expression).getArgs();
			}
			for (int i = 0; i < sub_expressions.length; i++) {
				Expr<?> sub_expression = sub_expressions[i];
				if (sub_expression.toString().contains(":var " + expected_variable_index)) {
					tracking_indexes.add(i);
					if (track_function_applications_until_quantified_variable(expected_variable_index, sub_expression,
							tracking_indexes)) {
						// If this recursive call returns true, then we found our variable and
						// tracking_indexes contains all the information we need to reconstruct the path
						// we used to get there.
						return true;
					}
					tracking_indexes.remove(tracking_indexes.size() - 1);
				}
			}
		}
		// If we reach this part of the code, then we didn't find our variable.
		return false;
	}

	// Recursively traverses the current_expression according to the contents of
	// tracking_indexes to find a concrete value. If the sort of that concrete value
	// matches the quantified_variable_sort, we give it to quant_vars so that it can
	// be added as a possible concrete value for quantified_variable_name.
	private void repeat_function_applications_until_concrete_value(Symbol quantified_variable_name,
			Sort quantified_variable_sort, Expr<?> current_expression, List<Integer> tracking_indexes) {
		if (tracking_indexes.isEmpty() || !current_expression.isApp()) {
			// If tracking_indexes is empty, then we should have reached our goal. That is,
			// the current_expression should be a concrete value that matches the
			// quantified_variable_sort. However, it can also happen that tracking_indexes
			// is not yet empty, even though we cannot "dive" deeper into the
			// current_expression (since it is not an application). This is the case when
			// parts of the expression are automatically simplified by Z3. To get around
			// this problem, we just assume that we have reached our concrete value anyway
			// and check if the current_expression matches the quantified_variable_sort.
			if (current_expression.getSort().equals(quantified_variable_sort)) {
				// If that's the case, we just found our pair of quantified variable and
				// concrete value.
				if (Setup.log_type == Log_Type.full) {
					verbal_output.add_to_buffer("[SUCCESS]", "The quantified variable " + quantified_variable_name
							+ " is instantiated with the concrete value " + current_expression + ".");
				}
				quant_vars.add_quantifier_instantiation(quantified_variable_name, current_expression.simplify());
			} else {
				// If that's not the case, then our tracking failed.
				if (Setup.log_type == Log_Type.full) {
					verbal_output.add_to_buffer("[PROBLEM]",
							"Failed tracking: Did not find a suitable concrete value where expected.");
				}
			}
		} else {
			// If there is another entry in tracking_indexes and we are able to do so, then
			// we "dive" further into the sub_expression of the current_expression indexed
			// by that entry if that's possible.
			int next_index = tracking_indexes.remove(0);
			Expr<?>[] sub_expressions = current_expression.getArgs();
			if (sub_expressions.length > next_index) {
				repeat_function_applications_until_concrete_value(quantified_variable_name, quantified_variable_sort,
						sub_expressions[next_index], tracking_indexes);
			} else {
				if (Setup.log_type == Log_Type.full) {
					verbal_output.add_to_buffer("[PROBLEM]",
							"Failed tracking: Could not dive into a non-existing sub-expression (out-of-bounds index).");
				}
			}
		}
	}

	// *****************************************************************************
	// Recovery-related methods.

	// Traverses the unsat-proof and collects all syntactically occurring
	// concrete values, which we can then consider as possible values for all
	// quantified variables of the same type.
	@Override
	public Proof_Concrete_Values collect_concrete_values() {
		Proof_Concrete_Values concrete_values = new Proof_Concrete_Values();
		collect_all_concrete_values(new Expr<?>[] { proof.getProofExpression() }, concrete_values);
		for (Expr<?> constant : input_reader.constants) {
			concrete_values.add(constant);
		}
		return concrete_values;
	}

	// Recursively traverses expressions to collect all possible concrete values.
	// Returns true if all elements of expressions are concrete values.
	private Boolean collect_all_concrete_values(Expr<?>[] expressions, Proof_Concrete_Values concrete_values) {
		Boolean encountered_only_concrete_values = true;
		for (Expr<?> expression : expressions) {
			if (expression.isVar()) {
				// Quantified variables are no concrete values.
				encountered_only_concrete_values = false;
				continue;
			}
			if (expression.simplify().getNumArgs() == 0) {
				// Constants (expressions with no arguments) are concrete values.
				concrete_values.add(expression);
			}
			if (expression.isApp()) {
				// Concrete values can also be function applications with other concrete values
				// as arguments. The following list contains all functions we consider for this.
				if (expression.getFuncDecl().getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED)
						|| expression.isAnd() || expression.isOr() || expression.isNot() || expression.isLE()
						|| expression.isGE() || expression.isLT() || expression.isGT() || expression.isAdd()
						|| expression.isSub() || expression.isUMinus() || expression.isMul()) {
					if (collect_all_concrete_values(expression.getArgs(), concrete_values)) {
						// If the current expression is one of our supported functions and all arguments
						// are concrete values, then this expression is as well a concrete value.
						concrete_values.add(expression);
					} else {
						// Otherwise, this is no concrete value.
						encountered_only_concrete_values = false;
					}
				}
			}
			// It can happen that concrete values appear only in the patterns of a
			// Quantifier, so we look at them too if the expression is a Quantifier.
			if (expression.isQuantifier() && ((Quantifier) expression).getNumPatterns() > 0) {
				Pattern[] patterns = ((Quantifier) expression).getPatterns();
				for (Pattern pattern : patterns) {
					Expr<?>[] pattern_arguments = pattern.getTerms();
					collect_all_concrete_values(pattern_arguments, concrete_values);
				}
			}
		}
		return encountered_only_concrete_values;
	}

	// *****************************************************************************
}