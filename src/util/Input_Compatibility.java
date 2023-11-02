/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import util.Verbal_Output.Log_Type;

/*
 * This class contains methods that are used to modify or create an SMT-LIBv2
 * input file (.smt2), so that it can be parsed by the respective prover and that
 * the code written in this project will succeed.
 */

public class Input_Compatibility {

	// Creates a modified copy of the input_file at "temp\z3_input.smt2".
	// The changes ensure that both the Z3 API and the code written in this project
	// do not throw exceptions when working with the input.
	// Returns the modified file.
	// Throws a Proof_Exception if it fails to rewrite the input.
	public static File make_z3_compatible(File input_file, Verbal_Output verbal_output) throws Proof_Exception {
		try {
			// First, we read the input from file and make some general modifications
			// (in the sense that we do them regardless of which prover we will use).
			List<String> modified_input = read_and_make_generally_compatible(input_file, verbal_output);
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]",
						"Will now preprocess the input file for reading it with the Z3 API.");
			}
			String fileName = String_Utility.get_file_name(input_file);
			// Next, we create a file for the modified input at
			// "temp\<file_name>_z3_input.smt2".
			String temp_file_path = "temp" + File.separator + fileName + "_z3_input.smt2";
			File temp_file = new File(temp_file_path);
			if (!temp_file.createNewFile()) {
				temp_file.delete();
				temp_file.createNewFile();
			}
			PrintStream output = new PrintStream(temp_file);
			for (String line : modified_input) {
				if (line.trim().equals("(set-option :smt.mbqi false)")) {
					// the benchmarks from the evaluation of the FM paper used E-matching, now we
					// need to enable MBQI
					output.println("(set-option :smt.mbqi true)");
					continue;
				}
				output.println(line);
			}
			output.close();
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]",
						"Finished modifying the input so that it can be processed by the Z3 API.");
				verbal_output.add_to_buffer("[INFO]", "New input file is at: " + temp_file_path + ".");
				verbal_output.print_buffer();
			}
			// Return the modified file.
			return temp_file;
		} catch (Exception e) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]", e.getMessage());
				verbal_output.add_all_to_buffer("\t", e.getStackTrace());
			}
			Exception_Handler.throw_proof_exception("Failed to rewrite the input file for Z3.", verbal_output);
		}
		// Unreachable.
		return null;
	}

	// Creates a modified copy of the input_file at "temp\vampire_input.smt2".
	// These changes ensure that both Vampire and the code written in this project
	// do not throw exceptions when working with the input.
	// Returns the modified file.
	// Throws a Proof_Exception if it fails to rewrite the input.
	public static File make_vampire_compatible(File input_file, Verbal_Output verbal_output) throws Proof_Exception {
		try {
			// First, we read the input from file and make some general modifications
			// (in the sense that we do them regardless of which prover we will use).
			List<String> modified_input = read_and_make_generally_compatible(input_file, verbal_output);
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]",
						"Will now preprocess the input file for proving it with Vampire.");
			}
			// Next, we create a file for the modified input at "temp\vampire_input.smt2".
			String temp_file_path = "temp" + File.separator + "vampire_input.smt2";
			File temp_file = new File(temp_file_path);
			if (!temp_file.createNewFile()) {
				temp_file.delete();
				temp_file.createNewFile();
			}
			PrintStream output = new PrintStream(temp_file);
			// Now, we are set to further modify the expressions and print them to output.
			for (String line : modified_input) {
				if (line.contains("check-sat") || line.contains("get-proof")) {
					if (Setup.log_type == Log_Type.full) {
						verbal_output.add_to_buffer("[INFO]", "Removed the line \"" + line + "\" from the input.");
					}
					continue;
				}
				// We modify each line so that it can be parsed by Vampire.
				String[] new_lines = String_Utility.vampirize(line);
				for (String new_line : new_lines) {
					output.println(new_line);
					if (!line.equals(new_line)) {
						if (Setup.log_type == Log_Type.full) {
							verbal_output.add_to_buffer("[INFO]", "Modified the following input line:");
							verbal_output.add_to_buffer("\t", "Old line: \"" + line + "\".");
							verbal_output.add_to_buffer("\t", "New line: \"" + new_line + "\".");
						}
					}
				}
			}
			output.close();
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[INFO]",
						"Finished modifying the input so that it can be processed by Vampire.");
				verbal_output.add_to_buffer("[INFO]", "New input file is at: " + temp_file_path + ".");
				verbal_output.print_buffer();
			}
			// Return the modified file.
			return temp_file;
		} catch (Exception e) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[PROBLEM]", e.getMessage());
				verbal_output.add_all_to_buffer("\t", e.getStackTrace());
			}
			Exception_Handler.throw_proof_exception("Failed to rewrite the input file for Vampire.", verbal_output);
		}
		// Unreachable.
		return null;
	}

	// Reads the input_file. Combines related lines in a single expression. Removes
	// comments and multiple successive spaces. Further handles ensures that the
	// input file and the Z3 API use the same random seeds.
	// Returns a list containing each relevant expression of the SMT-LIBv2 input.
	// Throws a Proof_Exception if it does not find the input_file.
	public static List<String> read_and_make_generally_compatible(File input_file, Verbal_Output verbal_output)
			throws Proof_Exception {
		verbal_output.add_to_buffer("[INFO]", "Will now generally preprocess the input file.");
		List<String> modified_input = new LinkedList<String>();
		// If the input file specifies random seeds, we adopt them, otherwise we use the
		// ones defined in Setup.java. We need to have the seeds in both the Z3 context
		// (because the Z3 API requires so) and the input file (because Vampire needs to
		// know the random seeds as well).
		Map<String, String> seeds = new HashMap<String, String>() {
			private static final long serialVersionUID = 2026514525742887229L;

			{
				put(Setup.sat_random_seed,
						"(set-option " + Setup.sat_random_seed + " " + Setup.get_sat_random_seed() + ")");
				put(Setup.smt_random_seed,
						"(set-option " + Setup.smt_random_seed + " " + Setup.get_smt_random_seed() + ")");
				put(Setup.nlsat_seed, "(set-option " + Setup.nlsat_seed + " " + Setup.get_nlsat_seed() + ")");
			}
		};
		try {
			// First, we set up a scanner to read the input from file.
			Scanner scanner = new Scanner(input_file);
			while (scanner.hasNextLine()) {
				String line = String_Utility.remove_comments(scanner.nextLine());
				if (line.isEmpty()) {
					continue;
				}
				// It is possible that one expression ranges over multiple lines in the
				// input_file. To detect such an occurrence, we compare the number of opening
				// and closing braces within the line.
				while (!String_Utility.has_balanced_braces(line)) {
					// If they are unequal, we just keep adding other lines until they are.
					if (scanner.hasNextLine()) {
						// However, we discard comments.
						line += String_Utility.remove_comments(scanner.nextLine());
					} else {
						// If the braces are still unbalanced but we have reached the end of the
						// input_file, the input is most likely syntactically incorrect and running the
						// prover will later result in an appropriate exception anyway.
						break;
					}
				}
				if (line.contains("set-info")) {
					// We ignore lines that set information.
					if (Setup.log_type == Log_Type.full) {
						verbal_output.add_to_buffer("[INFO]", "Removed the line \"" + line + "\" from the input.");
					}
					continue;
				}
				if (line.contains("set-option")) {
					// If the input files sets random seeds, we extract them.
					// If it does not, we set them according to the default.
					if (line.contains(Setup.sat_random_seed)) {
						try {
							String actual_seed = String_Utility.match_first(
									String_Utility.escape_metacharacters(Setup.sat_random_seed) + " \\d+\\)", line);
							actual_seed = actual_seed.substring(Setup.sat_random_seed.length() + 1,
									actual_seed.length() - 1);
							Setup.set_sat_random_seed(actual_seed);
							if (Setup.log_type == Log_Type.full) {
								verbal_output.add_to_buffer("[INFO]",
										"Set " + Setup.sat_random_seed + " to " + actual_seed + ".");
							}
							seeds.remove(Setup.sat_random_seed);
							modified_input.add(line);
							continue;
						} catch (Proof_Exception e) {
							if (Setup.log_type == Log_Type.full) {
								verbal_output.add_to_buffer("[PROBLEM]",
										"Failed to extract " + Setup.sat_random_seed + " from the input.");
							}
						}
					} else if (line.contains(Setup.smt_random_seed)) {
						try {
							String actual_seed = String_Utility.match_first(
									String_Utility.escape_metacharacters(Setup.smt_random_seed) + " \\d+\\)", line);
							actual_seed = actual_seed.substring(Setup.smt_random_seed.length() + 1,
									actual_seed.length() - 1);
							Setup.set_smt_random_seed(actual_seed);
							if (Setup.log_type == Log_Type.full) {
								verbal_output.add_to_buffer("[INFO]",
										"Set " + Setup.smt_random_seed + " to " + actual_seed + ".");
							}
							seeds.remove(Setup.smt_random_seed);
							modified_input.add(line);
							continue;
						} catch (Proof_Exception e) {
							if (Setup.log_type == Log_Type.full) {
								verbal_output.add_to_buffer("[PROBLEM]",
										"Failed to extract " + Setup.smt_random_seed + " from the input.");
							}
						}
					} else if (line.contains(Setup.nlsat_seed)) {
						try {
							String actual_seed = String_Utility.match_first(
									String_Utility.escape_metacharacters(Setup.nlsat_seed) + " \\d+\\)", line);
							actual_seed = actual_seed.substring(Setup.nlsat_seed.length() + 1,
									actual_seed.length() - 1);
							Setup.set_nlsat_seed(actual_seed);
							if (Setup.log_type == Log_Type.full) {
								verbal_output.add_to_buffer("[INFO]",
										"Set " + Setup.nlsat_seed + " to " + actual_seed + ".");
							}
							seeds.remove(Setup.nlsat_seed);
							modified_input.add(line);
							continue;
						} catch (Proof_Exception e) {
							if (Setup.log_type == Log_Type.full) {
								verbal_output.add_to_buffer("[PROBLEM]",
										"Failed to extract " + Setup.nlsat_seed + " from the input.");
							}
						}
					}
				}
				String new_line = line;
				if (new_line.contains("declare-fun") && new_line.contains("()")) {
					// We rewrite function-declarations without arguments to constant-declarations
					// to avoid confusion later in the evaluation. This helps us avoid duplicate
					// declarations that cause the Z3 API to throw an error when parsing.
					new_line = String_Utility.func_decl_to_const_decl(new_line);
				}
				// We remove vertical bars to avoid confusion later in the evaluation.
				new_line = String_Utility.remove_vertical_bars(new_line);
				// We remove multiple successive spaces (that may have been generated by
				// previous modifications).
				new_line = String_Utility.cleanup_spaces(new_line);
				if (new_line.isEmpty()) {
					// We skip lines that have become empty by the previous modifications (or
					// already were from the beginning).
					continue;
				}
				// If we reach this part, we can output the possibly modified line.
				modified_input.add(new_line);
				if (!line.equals(new_line)) {
					if (Setup.log_type == Log_Type.full) {
						verbal_output.add_to_buffer("[INFO]", "Modified the following input line:");
						verbal_output.add_to_buffer("\t", "Old line: \"" + line + "\".");
						verbal_output.add_to_buffer("\t", "New line: \"" + new_line + "\".");
					}
				}
			}
			scanner.close();
			// Finally, we add the seeds that have not been set by the input.
			for (String seed : seeds.keySet()) {
				modified_input.add(0, seeds.get(seed));
				if (Setup.log_type == Log_Type.full) {
					verbal_output.add_to_buffer("[INFO]", "Added the following line to the input: " + seeds.get(seed));
				}
			}
			if (Setup.log_type == Log_Type.full) {
				verbal_output.print_buffer();
			}
			return modified_input;
		} catch (FileNotFoundException e) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[PROBLEM]", e.getMessage());
				verbal_output.add_all_to_buffer("\t", e.getStackTrace());
			}
			Exception_Handler.throw_proof_exception("Failed to generally rewrite the input file.", verbal_output);
		}
		// Unreachable.
		return null;
	}

	// Creates an evaluation file at "temp\[output_file_name].smt2" that contains
	// (in this order):
	// - All declarations from the input_file.
	// - All constants in constant_declarations.
	// - All declarations in further_declarations that have not yet been declared.
	// - All assertions from the input_file that include no quantified variables.
	// - All assignments of concrete values to constants in constant_allocations.
	// - All instantiated quantifiers in quantifier_instantiations.
	public static File make_example(File input_file, Verbal_Output verbal_output, String output_file_name,
			Set<FuncDecl<?>> constant_declarations, Set<Expr<?>> constant_allocations,
			Set<String> quantifier_instantiations, Set<FuncDecl<?>> further_declarations) throws Proof_Exception {
		// We differ between declarations and assertions, because we want to ensure that
		// everything was declared before it may be possibly used in some assertion.
		Set<String> sort_declaration_print_buffer = new LinkedHashSet<String>();
		Set<String> declaration_print_buffer = new LinkedHashSet<String>();
		Set<String> assertion_print_buffer = new LinkedHashSet<String>();
		Scanner scanner;
		try {
			scanner = new Scanner(input_file);
			// First, we collect configurations, declarations and assertions from the
			// input_file.
			while (scanner.hasNext()) {
				String line = scanner.nextLine();
				if (line.contains("(declare-sort ") || line.contains("declare-datatype")) {
					sort_declaration_print_buffer.add(line);
				} else if (line.contains("(declare-fun ") || line.contains("(declare-const ")) {
					// Regarding the declarations, it may be that we never encountered them during
					// our analysis, but they are still needed for another part of the input that
					// will be included in the evaluation file.
					declaration_print_buffer.add(line);
				} else if (line.contains("(assert ") && !line.contains("(forall ")) {
					// Regarding the assertions, it is important to know that they do not appear at
					// all in the input parsed by the Z3 API but we still may need them if they do
					// not contain quantifiers, as they may also be part of the contradiction.
					assertion_print_buffer.add(line);
				}
			}
			scanner.close();
		} catch (FileNotFoundException e) {
			// This should actually be unreachable since we have already successfully read
			// the input_file in a previous stage of our proof analysis.
		}
		// Then, we use our sets to generate further declarations and assertions.
		for (FuncDecl<?> further_declaration : further_declarations) {
			String line = String_Utility.remove_line_breaks(further_declaration.toString());
			if (further_declaration.getArity() == 0) {
				// We want to declare constants as constants and not as functions without
				// arguments. This helps us avoid duplicate declarations that cause the Z3 API
				// to throw an error when parsing.
				line = String_Utility.func_decl_to_const_decl(line);
			}
			declaration_print_buffer.add(line);
		}
		// For each quantified variable, there as many associated constants in
		// constant_declarations as there were found possible values. If no possible
		// values were found for a quantified variable, we still declare one constant
		// because it might anyway passively occur in some Quantifier without actually
		// contributing to the contradiction.
		for (FuncDecl<?> constant_declaration : constant_declarations) {
			String line = String_Utility.remove_line_breaks(constant_declaration.toString());
			// Once more we rewrite the function-declarations without arguments to
			// constant-declarations to have the same form everywhere.
			line = String_Utility.func_decl_to_const_decl(line);
			declaration_print_buffer.add(line);
		}
		// Now, we assign our possible values to these constants we just declared.
		for (Expr<?> constant_allocation : constant_allocations) {
			String line = String_Utility.remove_line_breaks("(assert " + constant_allocation.toString() + ")");
			assertion_print_buffer.add(line);
		}
		// Finally, we have instantiated quantifiers that substitute the quantified
		// variables with all the possible combinations of constants corresponding to
		// each of those quantified variables.
		for (String quantifier_instantiation : quantifier_instantiations) {
			String line = String_Utility.remove_line_breaks("(assert " + quantifier_instantiation + ")");
			assertion_print_buffer.add(line);
		}
		// Then, we are set to actually create that evaluation file and fill it.
		try {
			// Create a temp_file to use for output.
			String temp_file_path = "temp" + File.separator + output_file_name + ".smt2";
			File temp_file = new File(temp_file_path);
			if (!temp_file.createNewFile()) {
				temp_file.delete();
				temp_file.createNewFile();
			}
			// Print the declarations and assertions we just made up to the temp_file.
			PrintStream output = new PrintStream(temp_file);
			// Put sort declarations at the beginning.
			sort_declaration_print_buffer.addAll(declaration_print_buffer);
			declaration_print_buffer = sort_declaration_print_buffer;
			for (String line : declaration_print_buffer) {
				output.println(line);
			}
			output.println();
			for (String line : assertion_print_buffer) {
				output.println(line);
			}
			output.close();
			// Also print the contents of our evaluation file to verbal_output.
			// verbal_output.print_evaluation_file_contents(temp_file,
			// declaration_print_buffer, assertion_print_buffer);
			// Return the path to the modified file.
			return temp_file;
		} catch (IOException e) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[PROBLEM]", e.getMessage());
				verbal_output.add_all_to_buffer("\t", e.getStackTrace());
			}
			Exception_Handler.throw_proof_exception("Failed to rewrite the input file for evaluation.", verbal_output);
		}
		// Unreachable.
		return null;
	}
}