/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proofanalyser;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Pattern;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import quantvar.Quant_Var;
import quantvar.Quant_Var_Handler;
import util.Exception_Handler;
import util.Input_Compatibility;
import util.Proof_Exception;
import util.Setup;
import util.String_Utility;
import util.Verbal_Output;
import util.Verbal_Output.Log_Type;

/*
 * This class is used to pre-process and read an SMT-LIBv2 input file (.smt2) and
 * set up the data structures that we need in a Proof_Analyser object. That is,
 * it collects everything related to quantified variables and their occurrence
 * within the input. It works with suitable data types from the Z3 API
 * (com.microsoft.z3). More concretely, it looks for the following things in the
 * input: 
 * - Quantified variables. 
 * - Uninterpreted functions that use quantified variables as arguments. 
 * - The names of all user-defined functions, constants and types.
 * 
 * Objects of this class should be created by the Proof_Analyser_Framework so
 * that the arguments of the constructor are set appropriately.
 */

public class Input_Reader {

	// The input is initially given in a file. We use multiple input files since we
	// modify the input for each of the supported provers.

	// File containing the input.
	// Is provided in the constructor.
	private File initial_input_file;

	// File containing the input modified for Z3.
	// Is null before the method z3_setup has been called.
	protected File z3_input_file;

	public File get_input_file() {
		return z3_input_file;
	}

	public File get_initial_input_file() {
		return initial_input_file;
	}

	// File containing the input modified for Vampire.
	// Is null before the method vampire_setup has been called.
	protected File vampire_input_file;

	// Takes care of printing results and intermediate steps.
	// Is initialized in the constructor based on the Output_Type and PrintStream
	// provided there.
	protected Verbal_Output verbal_output;

	// "The main interaction with Z3 happens via the Context. It maintains all data
	// structures related to terms and formulas that are created relative to them."
	// - from the Z3 API.
	// Is null before the method z3_setup has been called.
	protected Context context;

	// Contains the contents of the z3_input_file parsed by the Z3 SMT-LIBv2 parser.
	// Is null before the method z3_setup has been called.
	protected BoolExpr[] input;

	// For each quantified variable in the input, we create a Quant_Var object.
	// There, we remember all the information about this quantified variable
	// provided by the input, such as the associated input formula (in form of a
	// Z3-Quantifier) and the uninterpreted functions that use this quantified
	// variable as an argument.

	// Collects our Quant_Var objects and acts as a wrapper with some methods for
	// adding information to and later also getting information from them.
	// Is null before the method z3_setup has been called.
	// Is empty before the method analyze_input has been called.
	protected Quant_Var_Handler quant_vars;

	// In a Proof_Analyser object, we then use quant_vars to collect information
	// about quantifier instantiations (more details provided there).

	// Collects all declarations from the input.
	// Is null before the method z3_setup has been called.
	// Is empty before the method analyze_input has been called.
	protected Set<FuncDecl<?>> declarations;

	public Set<Expr<?>> constants;

	// We further collect all user-defined names. That is, the names of every
	// user-defined function, constant and type. We need them if our Proof_Analyser
	// object takes a syntactic approach, which is the case for the
	// Vampire_Proof_Analyser.

	// Contains the name of every uninterpreted function.
	// Is empty before the method analyze_input has been called.
	protected Set<String> function_names;

	// Contains the name of every user-defined constant.
	// Is empty before the method analyze_input has been called.
	protected Set<String> constant_names;

	// Contains the name of every user-defined type.
	// Is empty before the method analyze_input has been called.
	protected Set<String> type_names;

	// Do not call this constructor yourself but use the Proof_Analyser_Framework.
	protected Input_Reader(File input_file, Log_Type output_type, PrintStream out) {
		this.initial_input_file = input_file;
		this.verbal_output = new Verbal_Output(output_type, out);
		this.function_names = new LinkedHashSet<String>();
		this.constant_names = new LinkedHashSet<String>();
		this.type_names = new LinkedHashSet<String>();
		if (!Setup.testing_environment) {
			verbal_output.add_to_buffer("[INFO]", "Handling " + initial_input_file.toString() + ".");
			verbal_output.add_to_buffer("[INFO]", "Created an Input_Reader object.");
			verbal_output.print_buffer();
		}
	}

	// Sets up our data structures to be used by a Z3_Proof_Analyser.
	// Throws a Proof_Exception if it fails to parse the input.
	// Do not call this method yourself but use the Proof_Analyser_Framework.
	protected void z3_setup() throws Proof_Exception {
		// First, we set up the context for Z3.
		Map<String, String> context_settings = new HashMap<String, String>() {
			private static final long serialVersionUID = 1833909773703903296L;

			{
				put("auto_config", "false");
				// Z3 needs us to enable proof generation by using the API and not in the input
				// file, otherwise we get an error. All configurations in the input that cause
				// an error when using the Z3 API will be removed by the method
				// make_z3_compatible defined in the class Input_Compability.
				put("proof", "true");
				put("model", "false");
				put("rlimit", String.valueOf(Setup.z3_rlimit));
				// The seeds cannot be added to the context (Z3 API does not allow it), but will
				// be added to the solver in the Z3_Proof_Analyser.
			}
		};
		this.context = new Context(context_settings);
		this.quant_vars = new Quant_Var_Handler(verbal_output, context, this);
		this.declarations = new LinkedHashSet<FuncDecl<?>>();
		this.constants = new LinkedHashSet<Expr<?>>();
		// Next, we have to modify the input_file so that the method parseSMTLIB2File as
		// well as the code written in this project will succeed.
		this.z3_input_file = Input_Compatibility.make_z3_compatible(initial_input_file, verbal_output);
		// Now, we are set to parse the input.
		this.input = context.parseSMTLIB2File(z3_input_file.getAbsolutePath(), null, null, null, null);
		if (!Setup.testing_environment) {
			verbal_output.add_to_buffer("[INFO]", "Successfully parsed the input with the Z3 API.");
		}
	}

	// Sets up our data structures to be used by a Vampire_Proof_Analyser.
	// Throws a Proof_Exception if it fails to parse the input.
	// Do not call this method yourself but use the Proof_Analyser_Framework.
	protected void vampire_setup() throws Proof_Exception {
		// We do the z3_setup anyway to set up our data structures, because there is no
		// suitable API for Vampire. That is, even though we will later use Vampire to
		// prove the input, we still use the Z3 API to feed information to quant_vars,
		// which is way more reliable than using regular expressions from the beginning.
		z3_setup();
		// Next, we have to modify the input so that both Vampire and the code written
		// in this project will succeed.
		vampire_input_file = Input_Compatibility.make_vampire_compatible(z3_input_file, verbal_output);
		quant_vars.add_input_file(vampire_input_file);
	}

	// Counting for evaluation statistics.
	public int n_quantifiers = 0;

	// Feeds quant_vars with information that we find in the input.
	// Collects user-defined names in function_names, constant_names and type_names.
	// Throws a Proof_Exception if the input does not satisfy our assumptions:
	// - All quantified variables have unique names.
	// - There are no existential quantifiers.
	// Do not call this method yourself but use the Proof_Analyser_Framework.
	protected void analyze_input() throws Proof_Exception {
		// Regardless of which prover we will use later, we use the input parsed by the
		// Z3 API to collect our desired information. For simplicity we handle the
		// quantifiers and the names with two separate searches through the z3_program.

		for (Expr<?> expression : input) {
			String expression_as_string = expression.toString();
			if (!expression_as_string.contains("forall")) {
				continue;
			}
			Expr<?>[] expression_in_array = new Expr<?>[] { expression };
			find_quantifiers(expression_in_array, null, expression);
		}
		// Finally, we print what we encountered while looking at the input.
		if (!Setup.testing_environment) {
			verbal_output.print_input(initial_input_file, quant_vars);
			System.out.println("Number of input formulas: " + input.length);
			System.out.println("Number of quantifiers: " + n_quantifiers);
		}
	}

	// Recursively traverses all elements in expressions to find the ones that
	// define quantified variables. Adds a fresh Quant_Var and the corresponding
	// information to quant_vars for each quantified variable that is encountered.
	// Throws a Proof_Exception if the input does not satisfy our assumptions:
	// - All quantified variables have unique names.
	// - There are no existential quantifiers.
	private void find_quantifiers(Expr<?>[] expressions, Quantifier quantifier_parent, Expr<?> input_line)
			throws Proof_Exception {
		for (Expr<?> expression : expressions) {
			// Quantified expressions are marked as Z3_QUANTIFIER_AST.
			if (expression.isQuantifier()) {
				n_quantifiers++;
				if (!Setup.testing_environment) {
					verbal_output.add_to_buffer("[Info]",
							"Encountered an expression marked as Quantifier in the input: " + expression + ".");
				}
				// Cast expression to a Quantifier so we can use Quantifier methods.
				// This always succeeds because we checked for isQuantifier before.
				Quantifier quantifier = (Quantifier) expression;
				// We memorize all quantified variables declared in the expression. That is, for
				// each of them we create a Quant_Var object that is maintained by quant_vars.
				extract_quantified_variables(quantifier, quantifier_parent, input_line);
				// Next, we look for applications of uninterpreted functions with quantified
				// variables.
				BoolExpr body = quantifier.getBody();
				// We do not know how the body exactly looks like. It ranges from being a single
				// quantified variable up to some deeply nested expression. This is why we have
				// to recursively look into the (sub-)arguments of it to possibly find
				// applications of uninterpreted functions.
				Expr<?>[] body_in_array = new Expr<?>[] { body };
				find_function_applications(quantifier, body_in_array);
				collect_names(body_in_array);
				// Nested Quantifiers are a thing in Z3. That is, it is possible for a
				// Quantifier to
				// occur as an argument of some other Quantifier.
				if (body.isApp()) {
					// We therefore possibly look into the arguments of our quantifier to find
					// nested Quantifiers.
					if (body.toString().contains("forall")) {
						find_quantifiers(body.getArgs(), quantifier, input_line);
					}
				}
				// It can happen that applications of uninterpreted functions appear only in the
				// patterns of a Quantifier, so we look at them too.
				if (quantifier.getNumPatterns() > 0) {
					// First, we check if there are any patterns at all. If that's the case, then we
					// recursively look into them just as we did before with the body.
					Pattern[] patterns = quantifier.getPatterns();
					for (Pattern pattern : patterns) {
						Expr<?>[] pattern_arguments = pattern.getTerms();
						find_function_applications(quantifier, pattern_arguments);
					}
				}
			} else if (expression.isApp()) {
				// No matter whether the current_expression is marked as Z3_QUANTIFIER_AST or
				// not, it may contain a Quantifier somewhere in its arguments, which we
				// therefore recursively look at.
				if (expression.toString().contains("forall")) {
					find_quantifiers(expression.getArgs(), quantifier_parent, input_line);
				}
				find_function_applications(quantifier_parent, expression.getArgs());
			}
		}
	}

	// Creates a fresh Quant_Var object in quant_vars for each quantified variable
	// occurring in the quantifier.
	// Throws a Proof_Exception if the input does not satisfy our assumptions:
	// - All quantified variables have unique names.
	// - There are no existential quantifiers.
	private void extract_quantified_variables(Quantifier quantifier, Quantifier parent, Expr<?> input_line)
			throws Proof_Exception {
		if (quantifier.isExistential()) {
			// We assume that all quantifiers are universal due to preprocessing.
			Exception_Handler.throw_proof_exception(
					"Encountered an existential quantifier in the input, which is not supposed to happen due to preprocessing.",
					verbal_output);
		}
		Symbol[] quant_var_names = quantifier.getBoundVariableNames();
		Sort[] quant_vars_sorts = quantifier.getBoundVariableSorts();
		int len = quant_var_names.length;
		for (int i = 0; i < len; i++) {
			// The name at index i corresponds to the sort at index i.
			Symbol name = quant_var_names[i];
			Sort sort = quant_vars_sorts[i];
			if (quant_vars.add_new_quant_var(name, sort, input_line, i, quantifier, parent)) {
				if (!Setup.testing_environment) {
					verbal_output.add_to_buffer("[INFO]",
							"Found quantified variable " + name + " of type " + sort + ".");
				}
			} else {
				Exception_Handler.throw_proof_exception(
						"The input violated the assumption of unique names for quantified variables. There are multiple occurrences of a quantified variable called "
								+ name,
						verbal_output);
			}
		}
	}

	// Recursively looks for applications of uninterpreted functions in arguments
	// and gives them to quant_vars.
	private void find_function_applications(Quantifier quantifier, Expr<?>[] expressions) {
		for (Expr<?> expression : expressions) {
			// We look for applications of uninterpreted functions, which are applications
			// marked as Z3_OP_UNINTERPRETED and have more than 0 arguments.
			if (expression.isApp()) {
				FuncDecl<?> func_decl = expression.getFuncDecl();
				if (func_decl.getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED) && quantifier != null
						&& expression.getNumArgs() > 0) {
					declarations.add(func_decl);
					// We found an application of an uninterpreted function, which we give to
					// quant_vars. However, the variables in the application are not directly the
					// quantified variables, but some sort of local variables that reference the
					// actual quantified variables by using De-Bruijn indexing. We therefore replace
					// them by constants of the same name.
					// Example: The expression may be "(f :var 0)", where ":var 0" refers to some
					// quantified variable x0 declared in the quantifier. We therefore replace
					// ":var 0" in "(f :var 0)" by "x0" so that we can work with "(f x0)" instead.
					Expr<?> function_application = replace_quant_vars_with_constants(expression, quantifier);
					if (function_application != null) {
						quant_vars.add_function_application_from_input(function_application);
					}
					// Note that uninterpreted functions with zero arguments are constants, which we
					// ignore.
				} else if (expression.getNumArgs() == 0) {
					declarations.add(func_decl);
					constants.add(expression);
				}
				if (expression.getNumArgs() > 0) {
					// No matter whether the current expression is marked as Z3_OP_UNINTERPRETED or
					// not, it may contain an uninterpreted function somewhere in its
					// (sub-)arguments, which we therefore recursively look at.
					find_function_applications(quantifier, expression.getArgs());
				}
			}
		}
	}

	// Replaces all quantified variables in expression with constants of the same
	// name. Assumes that the expression is contained in the quantifier.
	// Returns null upon failing.
	private Expr<?> replace_quant_vars_with_constants(Expr<?> expression, Quantifier quantifier) {
		// First, we collect all the names and types of the bound variables that appear
		// in the quantifier and in possible parents.
		Symbol[] variables = quantifier.getBoundVariableNames();
		Sort[] types = quantifier.getBoundVariableSorts();
		int n = variables.length;
		// Then, for each of them we create a constant with the same name, and store
		// these in REVERSE order (due to De Bruijn indexing).
		Expr<?>[] constant_variables = new Expr<?>[variables.length];
		try {
			for (int i = 0; i < n; i++) {
				constant_variables[n - i - 1] = context.mkConst(variables[i].toString(), types[i]);
			}
			return expression.substituteVars(constant_variables);
		} catch (Z3Exception e) {
			return null;
		}

	}

	// Recursively traverses all elements in expressions to populate the sets that
	// collect user-defined names.
	private void collect_names(Expr<?>[] expressions) {
		for (Expr<?> expression : expressions) {
			if (expression.isApp()) {
				// Our expression is an application.
				// If it has type Z3_OP_UNINTERPRETED, then its name is user-defined.
				if (expression.getFuncDecl().getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED)) {
					Set<Sort> types = new LinkedHashSet<Sort>();
					if (expression.getNumArgs() > 0) {
						// We found an uninterpreted function.
						String function_name = expression.getFuncDecl().getName().toString();
						function_names.add(function_name);
						if (!Setup.testing_environment) {
							verbal_output.add_to_buffer("[INFO]", "Added " + function_name + " to function_names.");
						}
						for (Sort sort : expression.getFuncDecl().getDomain()) {
							types.add(sort);
						}
						types.add(expression.getFuncDecl().getRange());
					} else if (expression.getNumArgs() == 0) {
						// We found a user-defined constant.
						String constant_name = expression.getFuncDecl().getName().toString();
						constant_names.add(constant_name);
						if (!Setup.testing_environment) {
							verbal_output.add_to_buffer("[INFO]", "Added " + constant_name + " to constant_names.");
						}
						types.add(expression.getFuncDecl().getRange());
					}
					// Finally, we add the user-defined types that we found.
					for (Sort sort : types) {
						if (sort.getSortKind().equals(Z3_sort_kind.Z3_UNINTERPRETED_SORT)) {
							String new_type = sort.getName().toString();
							type_names.add(new_type);
							if (!Setup.testing_environment) {
								verbal_output.add_to_buffer("[INFO]", "Added " + new_type + " to type_names.");
							}
						}
					}
				}
				// Even if the type of the expression is not Z3_OP_UNINTERPRETED, we recursively
				// look into its arguments, as it is an application.
				collect_names(expression.getArgs());
				if (expression.isQuantifier() && ((Quantifier) expression).getNumPatterns() > 0) {
					// First, we check if there are any patterns at all. If that's the case, then we
					// also recursively look into them just as we did before with the body.
					Pattern[] patterns = ((Quantifier) expression).getPatterns();
					for (Pattern pattern : patterns) {
						Expr<?>[] pattern_arguments = pattern.getTerms();
						collect_names(pattern_arguments);
					}
				}
			}
		}
	}

	// The method below are used to generate triggering terms for E-Matching.

	protected List<Expr<?>> get_patterns() {
		List<Expr<?>> pattern_function_applications = new LinkedList<Expr<?>>();
		collect_patterns(input, pattern_function_applications);
		return pattern_function_applications;
	}

	private void collect_patterns(Expr<?>[] expressions, List<Expr<?>> accumulator) {
		for (Expr<?> expression : expressions) {
			if (expression.isQuantifier()) {
				Quantifier quantifier = (Quantifier) expression;
				if (quantifier.getNumPatterns() > 0) {
					Pattern[] patterns = quantifier.getPatterns();
					for (Pattern pattern : patterns) {
						Expr<?>[] pattern_arguments = pattern.getTerms();
						find_function_applications_in_pattern(quantifier, pattern_arguments, accumulator);
					}
				}
			} else if (expression.isApp()) {
				collect_patterns(expression.getArgs(), accumulator);
			}
		}
	}

	private void find_function_applications_in_pattern(Quantifier quantifier, Expr<?>[] patterns,
			List<Expr<?>> accumulator) {
		for (Expr<?> pattern : patterns) {
			if (pattern.getFuncDecl().getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED)) {
				Expr<?> function_application = replace_quant_vars_with_constants(pattern, quantifier);
				if (!accumulator.contains(function_application)) {
					accumulator.add(function_application);
				}
			}
		}
	}

	private boolean in_unsat_core(String assertion, BoolExpr[] unsat_core) {
		for (BoolExpr unsat_core_expr : unsat_core) {
			if (assertion.contains(unsat_core_expr.toString())) {
				return true;
			}
		}
		return false;
	}

	private boolean was_instantiated(String assertion, List<Quant_Var> quant_vars) {
		for (Quant_Var quant_var : quant_vars) {
			if (assertion.contains(quant_var.get_name().toString())) {
				return true;
			}
		}
		return false;
	}

	private String get_required_assertions(Set<String> assertions, Example example) {
		BoolExpr[] unsat_core = example.unsat_core;
		List<Quant_Var> quant_vars = example.get_instantiated_quant_vars();
		String required_assertions = "";
		for (String assertion : assertions) {
			if (required_assertions.contains(assertion)) {
				continue;
			}
			if (!assertion.contains("forall")) { // quantifier-free
				if (in_unsat_core(assertion, unsat_core)) {
					required_assertions += assertion + "\n";
				}
			} else if (was_instantiated(assertion, quant_vars)) {
				required_assertions += assertion + "\n";
			}
		}
		return required_assertions;

	}

	private String get_used_declarations(Set<String> declarations, String assertions) {
		String used_declarations = "";
		for (String declaration : declarations) {
			String name = declaration.replace("(declare-fun", "").replace("(declare-sort", "")
					.replace("(declare-const", "").replace("|", "").trim();
			if (name.contains(" ")) {
				name = name.substring(0, name.indexOf(" "));
			} else if (name.contains(")")) {
				name = name.substring(0, name.indexOf(")")); // constants
			}
			if (assertions.contains(name)) {
				used_declarations += declaration + "\n";
			}
		}
		return used_declarations;
	}

	public Boolean minimize(Example example) {
		Scanner scanner;
		try {
			scanner = new Scanner(this.z3_input_file);

			String minimized_input_name = String_Utility.get_file_name(this.initial_input_file) + "_minimized.smt2";
			String output_file_path = "output" + File.separator + minimized_input_name;
			File output_file = new File(output_file_path);
			if (!output_file.createNewFile()) {
				output_file.delete();
				output_file.createNewFile();
			}
			PrintStream output = new PrintStream(output_file);
			boolean found_assert = false;

			Set<String> assertions = new LinkedHashSet<String>();
			Set<String> declarations = new LinkedHashSet<String>();

			while (scanner.hasNextLine()) {
				String line = scanner.nextLine();
				if (line.isEmpty()) {
					continue;
				}
				if (!line.startsWith("(assert")) {
					if (line.startsWith("(declare-fun") || line.startsWith("(declare-sort")
							|| line.startsWith("(declare-const")) {
						declarations.add(line);
						continue;
					}
					if (found_assert) {
						// add the used declarations and the assertions instantiated in the example
						String instantiated_assertions = get_required_assertions(assertions, example);
						String used_declarations = get_used_declarations(declarations, instantiated_assertions);

						output.print(used_declarations);
						output.print(instantiated_assertions);
						found_assert = false;
					}
					output.println(line);
				} else {
					assertions.add(line);
					if (!found_assert) {
						found_assert = true;
					}
				}
			}
			output.close();
			scanner.close();
		} catch (IOException e) {
			return false;
		}
		return false;
	}
}