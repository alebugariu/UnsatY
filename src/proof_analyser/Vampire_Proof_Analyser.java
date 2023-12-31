/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proof_analyser;

import java.io.File;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import com.microsoft.z3.Expr;

import proof_analyser.unsat_proof.Proof_Analyser;
import proof_analyser.unsat_proof.Vampire_Unsat_Proof;
import quant_var.Quant_Var_Handler;
import recovery.Proof_Concrete_Values;
import util.Proof_Exception;
import util.Setup;
import util.String_Utility;
import util.Vampire_Runner;
import util.Vampire_to_Z3_Parser;
import util.Verbal_Output;
import util.Verbal_Output.Log_Type;

/*
 * This class is used to generate and analyze a Vampire unsat-proof and find
 * implicit instantiations of quantified variables in it. To do so, we rely on
 * the following heuristics:
 * 
 * - Uninterpreted Functions: We consider uninterpreted functions that use
 * quantified variables as arguments as implicit quantifier instantiations.
 * Concretely, we assume that the presence of a quantified variable x0 as an
 * argument of an uninterpreted function f (e.g. f(x0)) in either the input or
 * the unsat-proof combined with the presence of the same uninterpreted function
 * f with a concrete value as an argument (e.g. f(0)) later in the unsat-proof
 * may be an indication that the quantified variable x0 is implicitly
 * instantiated with that concrete value (e.g. x0 = 0).
 * 
 * - Inequalities: An unsat-proof generated by Vampire may prevent the
 * instantiation of a quantified variable with a certain concrete value, so to
 * speak, using the interpreted function !=, which we also consider as implicit
 * quantifier instantiation. Concretely, we take an occurrence of "X0 != c" as
 * an implicit instantiation of the quantified variable X0 with the concrete
 * value c.
 * 
 * - Comparisons: Finally, we consider cases where the unsat proof relates
 * different quantified variables to each other. Given two quantified variables
 * X0 and X1 in an unsat-proof generated by Vampire, the formula "X0 = X1 + 1"
 * can occur. Now, if another heuristic extracts an implicit quantifier
 * instantiation for X1 with a concrete value c, this also gives us an implicit
 * quantifier instantiation for X0 with c + 1. However, the generation of such
 * concrete values requires semantic reasoning. While technically our approach
 * only uses syntactic reasoning, we nevertheless implemented parts of this
 * heuristic. Namely, we support equalities such as the example provided above.
 * 
 * Since there is no suitable API for Vampire, we will do this syntactically
 * with the help of regular expressions and other string-based methods.
 * 
 * Objects of this class should be created by the Proof_Analyser_Framework so
 * that the arguments of the constructor are set appropriately.
 */

public class Vampire_Proof_Analyser implements Proof_Analyser {

	// File containing the input modified for Vampire.
	// Is provided by the Input_Reader in the constructor.
	private File input_file;

	// Takes care of printing results and intermediate steps.
	// Is provided by the Input_Reader in the constructor.
	private Verbal_Output verbal_output;

	// Contains further data structures we populated while looking at the input.
	// Is provided in the constructor.
	private Input_Reader input_reader;

	// Allows us to store and retrieve information about quantified variables.
	// Is provided by the Input_Reader in the constructor.
	// Will be modified by the methods here. Concretely, we will add further
	// information about quantifier instantiations.
	private Quant_Var_Handler quant_vars;

	// Contains each line of the unsat-proof generated by Vampire for the
	// input_file.
	// Is null before the method generate_unsat_proof() has been called.
	private Vampire_Unsat_Proof proof;

	// Contains all user-defined names from the input.
	// Is initialized and populated in the constructor.
	private Set<String> names;

	// Expects the input_reader to be already set up appropriately.
	// Do not call this constructor yourself but use the Proof_Analyser_Framework.
	protected Vampire_Proof_Analyser(Input_Reader input_reader) {
		this.input_file = input_reader.vampire_input_file;
		this.verbal_output = input_reader.verbal_output;
		this.input_reader = input_reader;
		this.quant_vars = input_reader.quant_vars;
		if (Setup.log_type == Log_Type.full) {
			verbal_output.add_to_buffer("[INFO]", "Created a Vampire_Proof_Analyser object.");
		}
		// Create the names set.
		names = new LinkedHashSet<String>();
		names.addAll(input_reader.function_names);
		names.addAll(input_reader.constant_names);
		for (String sort : input_reader.type_names) {
			// We attach "()" to uninterpreted types (e.g. "ISeq()"), because that's how
			// Vampire expresses them.
			names.add(sort + "()");
		}
		quant_vars.add_names(names);
		if (Setup.log_type == Log_Type.full) {
			verbal_output.add_to_buffer("[INFO]",
					"Collected and modified the following user-defined names to be used in our regular expressions: "
							+ names.toString() + ".");
		}
		quant_vars.setup_parser(input_reader.declarations);
	}

	// Uses Vampire to generate an unsat-proof for the input_file and stores it in
	// the proof set.
	@Override
	public void generate_unsat_proof() throws Proof_Exception {
		proof = Vampire_Runner.run_vampire(input_file, names, verbal_output);
		if (Setup.log_type == Log_Type.full) {
			verbal_output.add_to_buffer("[INFO]", "Successfully generated an unsat-proof with Vampire.");
		}
	}

	// Looks for implicit quantifier instantiations in the generated proof and gives
	// them to quant_vars.
	// Throws a Proof_Exception if Vampire cannot prove unsat within the resources
	// defined in the class Setup.
	// Returns quant_vars.
	@Override
	public Quant_Var_Handler extract_quantifier_instantiations() throws Proof_Exception {
		DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
		LocalDateTime now = LocalDateTime.now();
		System.out.println("Vampire generated the unsat proof: " + dtf.format(now));
		// Next, we traverse the proof to match the quantified variables from the proof
		// to the ones from the input. We need to do this because Vampire tends to
		// rename quantified variables (and unify them).
		List<String> lines = proof.getLines();
		for (String line : lines) {
			match_quantified_variables(line);
		}
		// Then, we are set to look for quantifier instantiations. We do this in two
		// runs, where the first one consider function applications and inequalities,
		// and only after we consider comparisons, because the latter ones may rely on
		// the information found by the others.
		if (Setup.log_type == Log_Type.full) {
			verbal_output.add_to_buffer("[INFO]",
					"We will now traverse the unsat-proof to extract implicit quantifier instantiations.");
		}
		for (String line : lines) {
			String line_number = String_Utility.get_line_number(line);
			List<String> reference_numbers = String_Utility.get_line_reference_numbers(line);
			quant_vars.update_reference_numbers(line_number, reference_numbers);
		}
		for (String line : lines) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]",
						"We will now extract function applications and inequalities from the line " + line + ".");
			}
			find_function_applications(line);
			find_inequalities(line);
		}
		for (String line : lines) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]", "We will now extract comparisons from the line " + line + ".");
			}
			find_equalities(line);
		}

		// Print what we encountered while looking at the unsat-proof.
		verbal_output.print_prove(quant_vars);
		return quant_vars;
	}

	// Finds the names and types of all quantified variables occurring in the line.
	// These might be different from the ones that appear in the input. We therefore
	// give them to quant_vars, which matches them to the quantified variables we
	// encountered in the input.
	private void match_quantified_variables(String line) {
		// First, we want to find the number of that line within the proof. We need it
		// because whenever another proof step uses this line as a premise, that number
		// will be included in the references of that other proof step.
		String line_number = String_Utility.get_line_number(line);
		if (line_number.equals("")) {
			// There are some lines in the Vampire proof like:
			// "% Refutation found. Thanks to Tanya!".
			// These do not contain a number or a reference nor do they contribute to the
			// proof, so we just ignore them.
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]", "Skipped the line: \"" + line + "\".");
			}
			return;
		}
		// Next, we want to know what our line references (i.e. the premises).
		// Proof rules other than "input" usually come with one or several line numbers
		// referencing the premises.
		List<String> reference_numbers = String_Utility.get_line_reference_numbers(line);
		// Finally, we look for quantified variables that possibly occur in this line.
		List<String[]> line_quant_vars = String_Utility.get_line_quantified_variables_and_types(line);
		for (int i = 0; i < line_quant_vars.size(); i++) {
			String[] line_quant_var = line_quant_vars.get(i);
			String name = line_quant_var[0];
			String type = line_quant_var[1];
			if (line.contains("[input]") && reference_numbers.isEmpty()) {
				if (Setup.log_type == Log_Type.full) {
					verbal_output.add_to_buffer("[INFO]", "Found new quantified variable " + name + " of type " + type
							+ " in line " + line_number + " of the Vampire proof: " + line);
				}
				quant_vars.add_new_vampire_quantvar(line, i, name, type, line_number, reference_numbers);
			}
		}
	}

	// Finds occurrences of uninterpreted functions in the line and gives them to
	// quant_vars, which uses them to find implicit quantifier instantiations.
	private void find_function_applications(String line) {
		// Match occurrences of (possibly nested) function applications.
		for (String f_name : input_reader.function_names) {
			if (line.contains(f_name)) {
				List<String> function_applications = String_Utility.extract_function_applications(line, f_name);
				// Then, we give each function application to quant_vars.
				for (String function_application : function_applications) {
					quant_vars.add_concrete_values_from_function_application(f_name, function_application);
				}
			}
		}
	}

	// Finds inequalities in the line where one side is a quantified variable and
	// the other a concrete value.
	// Example: "7 != X0".
	private void find_inequalities(String line) {
		String line_number = String_Utility.get_line_number(line);
		for (String vampire_name : quant_vars.get_vampire_quant_var_names()) {
			for (String concrete_value : String_Utility.extract_inequalities(vampire_name, line)) {
				quant_vars.add_concrete_value_from_inequality(vampire_name, concrete_value, line_number);
			}
		}
	}

	// Finds pairs of quantified variables that are related to each other (with
	// equality) in the line and gives them to quant_vars, which uses them to find
	// implicit quantifier instantiations.
	// Example: "X1 = X0 + 1".
	private void find_equalities(String line) {
		String line_number = String_Utility.get_line_number(line);
		for (String vampire_name_1 : quant_vars.get_vampire_quant_var_names()) {
			for (String vampire_name_2 : quant_vars.get_vampire_quant_var_names()) {
				if (!vampire_name_1.equals(vampire_name_2)) {
					for (String term : String_Utility.extract_comparisons(vampire_name_1, vampire_name_2, line)) {
						quant_vars.add_comparison(term, vampire_name_1, vampire_name_2, line_number);
					}
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
		Vampire_to_Z3_Parser parser = new Vampire_to_Z3_Parser(input_reader.context, input_reader.declarations);
		Proof_Concrete_Values concrete_values = new Proof_Concrete_Values();
		List<String> lines = proof.getLines();
		for (String line : lines) {
			collect_all_concrete_values(line, concrete_values, parser);
		}
		for (Expr<?> constant : input_reader.constants) {
			concrete_values.add(constant);
		}
		return concrete_values;
	}

	// Checks each substring of the line to collect all possible concrete values.
	private void collect_all_concrete_values(String line, Proof_Concrete_Values concrete_values,
			Vampire_to_Z3_Parser parser) {
		try {
			line = String_Utility.match_first(". .*\\[", line);
		} catch (Proof_Exception e) {
			return;
		}
		for (int i = 0; i < line.length(); i++) {
			for (int j = i; j < line.length(); j++) {
				// We consider each possible substring of the line and check whether it can be a
				// concrete value. At this point, we consider an expression as a concrete value
				// if the Basic_Expr_Parser can parse it.
				Expr<?> parsed_expression = parser.parse_to_expr(line.substring(i, j));
				if (parsed_expression != null) {
					concrete_values.add(parsed_expression);
				}
			}
		}
	}

	@Override
	public int get_proof_size() {
		return proof.get_size();
	}

	// *****************************************************************************
}