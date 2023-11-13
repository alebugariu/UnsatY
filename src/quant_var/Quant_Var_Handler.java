/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package quant_var;

import java.io.File;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_decl_kind;

import recovery.Default_Values;
import util.Proof_Exception;
import util.Setup;
import util.String_Utility;
import util.Vampire_to_Z3_Parser;
import util.Verbal_Output;
import util.Verbal_Output.Log_Type;
import util.wrapper.Pattern_Wrapper;

/*
 * This class is used to maintain the information about quantified variables
 * from the input and from the unsat-proof through a set of Quant_Var objects.
 * It contains methods for adding and retrieving information to and from them
 * and for quantifier instantiation.
 */

public class Quant_Var_Handler {

	// Takes care of printing results and intermediate steps.
	// Is provided in the constructor.
	public Verbal_Output verbal_output;

	// "The main interaction with Z3 happens via the Context. It maintains all data
	// structures related to terms and formulas that are created relative to them."
	// - from the Z3 API.
	// Is provided in the constructor.
	protected Context context;

	// Contains all Quant_Var objects that are maintained.
	// Is initialized in the constructor.
	// Elements are continuously added and modified by the methods below.
	private Set<Quant_Var> quant_vars;

	private Map<String, Quant_Var> names_to_quant_vars;

	// Maps the quantified formulas from the input to a set of top-level quantifiers
	// appearing in them (that is, it does not include the nested quantifiers)
	// We us them when constructing a potential example.
	// Is initialized in the constructor.
	// Elements are continuously added by the add_new_quant_var method.
	private Map<Expr<?>, Set<Quantifier>> quantified_input_formulas;

	private Set<Quantifier> nested_quantifiers;

	private int dummy_function_counter = 0;

	private Default_Values defaults;

	public Quant_Var_Handler(Verbal_Output verbal_output, Context context) {
		this.verbal_output = verbal_output;
		this.context = context;
		this.quant_vars = new LinkedHashSet<Quant_Var>();
		this.names_to_quant_vars = new HashMap<String, Quant_Var>();
		this.quantified_input_formulas = new HashMap<Expr<?>, Set<Quantifier>>();
		this.nested_quantifiers = new LinkedHashSet<Quantifier>();
		this.defaults = new Default_Values();
	}

	public Set<Quant_Var> get_quant_vars() {
		return quant_vars;
	}

	public boolean exists(String quant_var_name) {
		return names_to_quant_vars.containsKey(quant_var_name);
	}

	// *****************************************************************************
	// Input-related methods and fields.

	// Creates a fresh Quant_Var object from scratch and adds it to quant_vars.
	// Adds the input_formula to the keyset of quantified_input_formulas (if not
	// already present) and the quantifier to its values.
	// Returns true if the string representation of the name is unique and therefore
	// this quantified variable satisfies our assumptions.
	public Boolean add_new_quant_var(Symbol name, Sort type, Expr<?> input_formula, int number_in_input_formula,
			Quantifier quantifier, Quantifier parent) {
		String var_name = name.toString();
		Quant_Var quant_var = names_to_quant_vars.get(var_name);
		if (quant_var != null && !quant_var.quantifier.equals(quantifier)) {
			// If the new quantified variable has the same name as another one we already
			// encountered and they are from different quantifiers, then the input violates
			// our assumptions.
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[ERROR]", "The quantified variable " + var_name
						+ " is used by the input for multiple different quantified variables.");
			}
			return false;
		}
		// If our assumptions are satisfied, we create add a fresh Quant_Var object.
		quant_var = new Quant_Var(var_name, type, input_formula, number_in_input_formula, quantifier, verbal_output);
		quant_vars.add(quant_var);
		names_to_quant_vars.put(var_name, quant_var);
		if (!quantified_input_formulas.keySet().contains(input_formula)) {
			Set<Quantifier> quantifiers = new LinkedHashSet<Quantifier>();
			quantifiers.add(quantifier);
			quantified_input_formulas.put(input_formula, quantifiers);
		} else {
			if (parent == null) {
				quantified_input_formulas.get(input_formula).add(quantifier);
			}
		}
		if (parent != null) {
			nested_quantifiers.add(parent);
		}
		return true;
	}

	// Adds the function_application to each element in quant_vars whose
	// corresponding quantified variable appears in it.
	// Assumes that the local variables in f_application have been replaced by
	// constants, whose names match the ones of the quantified variables.
	// Example: Instead of f((:var 0) + 3), we have f(x0 + 3), where x0 is a
	// constant that has the same name as the quantified variable that (:var 0)
	// references in the expression from which we extracted that function
	// application (this is done in the Input_Reader).
	public void add_function_application_from_input(Expr<?> function_application) {
		if (!function_application.isApp()
				|| !function_application.getFuncDecl().getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED)
				|| !(function_application.getNumArgs() > 0)) {
			// This is not an application of an uninterpreted function.
			return;
		}
		Expr<?>[] arguments = function_application.getArgs();
		for (Expr<?> argument : arguments) {
			// We recursively traverse the arguments to find quantified variables
			// (represented by constants of the same name) and add the function_application
			// to the corresponding element in quant_vars.
			// Example: If function_application is f(x0 + 3), then we eventually find x0 and
			// add it to the corresponding element in quant_vars.
			add_function_application_argument_from_input(function_application.getFuncDecl(), function_application,
					argument);
		}
	}

	// Recursively traverses the function_application to look for constants whose
	// names correspond to the ones of the quantified variables. Upon finding one
	// gives the function_application to the corresponding element in quant_vars.
	private void add_function_application_argument_from_input(FuncDecl<?> f_decl, Expr<?> function_application,
			Expr<?> current_argument) {
		// The current_argument may either be just a constant or an
		// expression that contains (possibly multiple) constants.
		if (current_argument.isConst()) {
			// This is the case where the current_argument is just a constant.
			for (Quant_Var quant_var : quant_vars) {
				quant_var.add_function_application_from_input(f_decl, function_application, current_argument);
			}
		} else if (current_argument.isApp()) {
			// This is the case where the current_argument is an expression, which is why we
			// recursively look into its arguments.
			if (current_argument.getFuncDecl().getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED)) {
				// If it is another uninterpreted function, then we consider this one, as we are
				// always only interested in the innermost uninterpreted function when
				// considering function applications for implicit quantifier instantiations.
				for (Expr<?> argument : current_argument.getArgs()) {
					add_function_application_argument_from_input(current_argument.getFuncDecl(), current_argument,
							argument);
				}
			} else {
				// Otherwise, we keep the initial function declaration.
				for (Expr<?> argument : current_argument.getArgs()) {
					add_function_application_argument_from_input(f_decl, function_application, argument);
				}
			}
		}
		// If it is neither a constant nor an application, then it is not
		// interesting for our purposes.
	}

	// *****************************************************************************

	// *****************************************************************************
	// Vampire_Quant_Var-related methods and fields.

	// We need the input file when translating input lines to Vampire proof syntax
	// (in the method add_new_vampire_quantvar).
	// Is null before the method add_input_file has been called.
	File input_file;

	// We can only add the input_file after we did the preprocessing for Vampire,
	// which happens after the Quant_Var_Handler object has been initialized.
	public void add_input_file(File input_file) {
		this.input_file = input_file;
	}

	// Contains all user-defined names from the input.
	// Is null before the method add_names has been called.
	private Set<String> names;

	// If you are using a Vampire_Proof_Analyser, then this method is called in its
	// constructor to appropriately add the names.
	public void add_names(Set<String> names) {
		this.names = names;
	}

	// Given some information about a quantified variable in an unsat-proof
	// generated by Vampire, we find the corresponding element in quant_vars from
	// the input and transform it into a Vampire_Quant_Var object.
	// Modifies the quant_vars list.
	public void add_new_vampire_quantvar(String line, int number_in_input_formula, String name, String type,
			String line_number, List<String> reference_numbers) {
		try {
			// We only add a "new" Vampire_Quant_Var object if the corresponding line is
			// tagged as [input] and has no references, that is, the quantified variable is
			// really used for the first time in the proof.
			if (line.contains("[input]") && reference_numbers.isEmpty()) {
				// If that's the case, then we use Vampire at runtime to translate each
				// input formula into Vampire proof syntax and find the best match for the line
				// from the unsat-proof.
				Map<String, Set<Quant_Var>> vampirized_input_formulas = new HashMap<String, Set<Quant_Var>>();
				for (Quant_Var quant_var : quant_vars) {
					String vampirized_input_formula = quant_var.vampirize_input_formula(input_file, names);
					// Since multiple quantified variables may appear in the same input formula, we
					// must remember all of them that do so.
					if (!vampirized_input_formulas.containsKey(vampirized_input_formula)) {
						Set<Quant_Var> input_formula_quant_vars = new LinkedHashSet<Quant_Var>();
						input_formula_quant_vars.add(quant_var);
						vampirized_input_formulas.put(vampirized_input_formula, input_formula_quant_vars);
					} else {
						vampirized_input_formulas.get(vampirized_input_formula).add(quant_var);
					}
				}
				// We then search for the best match by computing the edit distance for all
				// possible candidates. This is necessary because Vampire does not necessarily
				// produce exactly the same line twice (in terms of naming, for example), but
				// the actual input line we are looking for still has the smallest editing
				// distance since those changes affect all candidates.
				line = String_Utility.simplify_preprocessing_line(line);
				String vampirized_input_formula = String_Utility.get_min_dist_string(line,
						vampirized_input_formulas.keySet());
				for (Quant_Var quant_var : vampirized_input_formulas.get(vampirized_input_formula)) {
					if (quant_var.number_in_input_formula == number_in_input_formula) {
						// If the quantified variable we are adding has the same number has the
						// quant_var we currently look and, then we found our match.
						if (Setup.log_type == Log_Type.full) {
							verbal_output.add_to_buffer("[INFO]",
									"Mapped the quantified variable " + name + " from the vampire-proof in line "
											+ line_number + " to the quantified variable " + quant_var.get_name()
											+ " from the input.");
						}
						quant_vars.remove(quant_var);
						quant_vars.add(new Vampire_Quant_Var(quant_var, name, type, line_number));
					}
				}
			}
		} catch (Proof_Exception e) {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[PROBLEM]", "Failed to add the Vampire_Quant_Var " + name + ".");
			}
		}
	}

	// Returns a set of all vampire_names of elements in quant_vars.
	public Set<String> get_vampire_quant_var_names() {
		Set<String> out = new LinkedHashSet<String>();
		for (Quant_Var quant_var : quant_vars) {
			if (quant_var.is_vampire_quant_var()) {
				out.add(((Vampire_Quant_Var) quant_var).get_vampire_name());
			}
		}
		return out;
	}

	// *****************************************************************************

	// *****************************************************************************
	// Z3_Proof_Analyser-related methods.

	// Adds the value to the quantified variable.
	// Sets the is_explicitly_instantiated flag for that quant_var.
	public void add_quantifier_instantiation(Symbol var, Expr<?> value) {
		Quant_Var quant_var = names_to_quant_vars.get(var.toString());
		quant_var.add_concrete_value(value);
		quant_var.is_explicitly_instantiated = true;
	}

	// *****************************************************************************

	// *****************************************************************************
	// Vampire_Proof_Analyser-related methods and fields.

	// Can be used to parse Strings to Expr<?>.
	// Is null before the method setup_parser has been called.
	private Vampire_to_Z3_Parser parser;

	// We can only setup the parser once we collected all function declarations from
	// the input, as the parser relies on them to parse function applications.
	public void setup_parser(Set<FuncDecl<?>> function_declarations) {
		parser = new Vampire_to_Z3_Parser(context, function_declarations);
	}

	// Adds value to each element in quant_vars that has the same type and has not
	// been explicitly instantiated.
	public void add_concrete_value(Expr<?> value) {
		for (Quant_Var quant_var : quant_vars) {
			if (!quant_var.is_explicitly_instantiated) {
				try {
					if (quant_var.get_type().equals(value.getSort())) {
						quant_var.add_concrete_value(value);
					}
				} catch (Z3Exception e) {
					if (Setup.log_type == Log_Type.full) {
						verbal_output.add_to_buffer("[PROBLEM]", "Tried to add the possible value " + value
								+ " that has unknown type to the quantified variable " + quant_var.get_name() + ".");
					}
				}
			}
		}
	}

	// Adds line_number to each element in quant_vars that already contains at least
	// one of the reference_numbers.
	public void update_reference_numbers(String line_number, List<String> reference_numbers) {
		for (Quant_Var quant_var : quant_vars) {
			if (quant_var.is_vampire_quant_var()) {
				Vampire_Quant_Var vampire_quant_var = (Vampire_Quant_Var) quant_var;
				for (String reference_number : reference_numbers) {
					if (vampire_quant_var.contains_line_number(reference_number)) {
						vampire_quant_var.line_numbers.add(line_number);
						break;
					}
				}
			}
		}
	}

	// Gives the function_application to all elements in quant_vars that are used by
	// f_name as an argument.
	// Assumes that setup_parser has been called before, i.e., parser is non-null.
	public void add_concrete_values_from_function_application(String f_name, String function_application) {
		Expr<?> parsed_function_application = parser.parse_to_expr(function_application);
		if (parsed_function_application != null) {
			for (Quant_Var quant_var : quant_vars) {
				if (quant_var.contains_function_declaration(f_name) && quant_var.is_vampire_quant_var()) {
					try {
						if (quant_var.get_type().equals(parsed_function_application.getSort())) {
							((Vampire_Quant_Var) quant_var).add_concrete_value_from_function_application(
									parsed_function_application, verbal_output);
						}
					} catch (Z3Exception e) {
						if (Setup.log_type == Log_Type.full) {
							verbal_output.add_to_buffer("[PROBLEM]",
									"Tried to add the possible value " + parsed_function_application
											+ " that has unknown type to the quantified variable "
											+ quant_var.get_name() + ".");
						}
					}
				}
			}
		} else {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[PROBLEM]",
						"Failed to parse the function application " + function_application + " to a Z3 Expr<?>.");
			}
		}
	}

	// Parses the concrete_value to and Expr<?> and gives it to all elements in
	// quant_vars that are called vampire_name and contain the line_number.
	// Assumes that setup_parser has been called before, i.e., parser is non-null.
	public void add_concrete_value_from_inequality(String vampire_name, String concrete_value, String line_number) {
		Expr<?> parsed_concrete_value = parser.parse_to_expr(concrete_value);
		if (parsed_concrete_value != null) {
			for (Quant_Var quant_var : quant_vars) {
				if (quant_var.is_vampire_quant_var()
						&& ((Vampire_Quant_Var) quant_var).get_vampire_name().equals(vampire_name)
						&& ((Vampire_Quant_Var) quant_var).contains_line_number(line_number)) {
					try {
						if (quant_var.get_type().equals(parsed_concrete_value.getSort())) {
							quant_var.add_concrete_value(parsed_concrete_value);
						}
					} catch (Z3Exception e) {
						if (Setup.log_type == Log_Type.full) {
							verbal_output.add_to_buffer("[PROBLEM]",
									"Tried to add the possible value " + parsed_concrete_value
											+ " that has unknown type to the quantified variable "
											+ quant_var.get_name() + ".");
						}
					}
				}
			}
		} else {
			if (Setup.log_type == Log_Type.full) {
				verbal_output.add_to_buffer("[PROBLEM]",
						"Failed to parse the concrete value " + concrete_value + " to a Z3 Expr<?>.");
			}
		}
	}

	// Uses the concrete values for all elements in quant_vars called vampire_name_2
	// (and that containing line_number) to replace all its occurrences in the term,
	// and then gives the instantiated term to all elements in quant_vars called
	// vampire_name_1 (and that containing line_number) as concrete values.
	// Assumes that setup_parser has been called before, i.e., parser is non-null.
	public void add_comparison(String term, String vampire_name_1, String vampire_name_2, String line_number) {
		for (Quant_Var quant_var : quant_vars) {
			if (quant_var.is_vampire_quant_var()
					&& ((Vampire_Quant_Var) quant_var).get_vampire_name().equals(vampire_name_2)) {
				for (Expr<?> concrete_value : quant_var.concrete_values) {
					// First, we syntactically replace each occurrence of vampire_name_2 in the term
					// by the current concrete_value.
					String instantiated_term = term.replace(vampire_name_2, concrete_value.toString());
					// Then, we parse the instantiated_term to a Z3 Expr<?>.
					Expr<?> parsed_concrete_value = parser.parse_to_expr(instantiated_term).simplify();
					if (parsed_concrete_value != null) {
						// If we were successful, we add the concrete value to each element in
						// quant_vars that is called vampire_name_1, contains line_number and has the
						// same type as the parsed_concrete_value.
						for (Quant_Var other_quant_var : quant_vars) {
							if (other_quant_var.is_vampire_quant_var()
									&& ((Vampire_Quant_Var) other_quant_var).get_vampire_name().equals(vampire_name_1)
									&& ((Vampire_Quant_Var) quant_var).contains_line_number(line_number)) {
								try {
									if (other_quant_var.get_type().equals(parsed_concrete_value.getSort())) {
										other_quant_var.add_concrete_value(parsed_concrete_value);
									}
								} catch (Z3Exception e) {
									if (Setup.log_type == Log_Type.full) {
										verbal_output.add_to_buffer("[PROBLEM]",
												"Tried to add the possible value " + parsed_concrete_value
														+ " that has unknown type to the quantified variable "
														+ other_quant_var.get_name() + ".");
									}
								}
							}
						}
					} else {
						if (Setup.log_type == Log_Type.full) {
							verbal_output.add_to_buffer("[PROBLEM]",
									"Failed to parse the concrete value " + concrete_value + " to a Z3 Expr<?>.");
						}
					}
				}
			}
		}
	}

	// *****************************************************************************

	// *****************************************************************************
	// Methods and fields for constructing potential examples.

	// Maps the string-representation of a quantified variable to a list of
	// constants corresponding to that quantified variable.
	// The methods below use these constants.
	// Is null before the method make_constants has been called.
	private Map<Quant_Var, List<Expr<?>>> possible_constants;

	// Initializes and populates possible_constants.
	private void make_constants(Context context) {
		possible_constants = new HashMap<Quant_Var, List<Expr<?>>>();
		for (Quant_Var quant_var : quant_vars) {
			possible_constants.put(quant_var, quant_var.make_constants(context));
		}
	}

	// For each element in quant_vars, we create as many constants as we found
	// possible concrete values. If we have not found any possible value, then we
	// still create a single associated constant. We need this for the case where
	// this non-instantiated quantified variable occurs passively in a quantifier,
	// that is, it is syntactically present, but irrelevant for the contradiction.

	// Contains the declarations of these constants we just described.
	// Is null before the method make_assertions has been called.
	public Set<FuncDecl<?>> constant_declarations;

	// Contains assignments of concrete values to the constants in
	// constant_declarations.
	// Is null before make_assertions has been called.
	public Set<Expr<?>> constant_allocations;

	// Contains the input formulas that we instantiate.
	// Is null before make_assertions has been called.
	public Set<String> instantiated_formulas;

	// Contains further declarations for some expressions in constant_allocations
	// and instantiated_formulas.
	// Is null before make_assertions has been called.
	public Set<FuncDecl<?>> further_declarations;

	// Uses the concrete values we extracted from the unsat-proofs to instantiate
	// some of the quantifiers from the input.
	// Generates all declarations and expressions required in a potential example
	// and stores them in constant_declarations, constant_allocations,
	// instantiated_formulas and further_declarations.
	// Do not call this method yourself but use your Evaluator object.
	public void make_assertions(Context context) throws Proof_Exception {
		// Initialize our sets and map.
		make_constants(context);
		constant_declarations = new LinkedHashSet<FuncDecl<?>>();
		constant_allocations = new LinkedHashSet<Expr<?>>();
		instantiated_formulas = new LinkedHashSet<String>();
		further_declarations = new LinkedHashSet<FuncDecl<?>>();
		for (Expr<?> quantified_input_formula : quantified_input_formulas.keySet()) {
			// We instantiate each quantifier that appears in sequence in the input formula
			// separately, along with any nested quantifiers it may contain.

			// Example: If the input formula is shaped as:
			// (forall x0: ...) and (forall x1: ...(forall x2: ...)...),
			// then we instantiate the quantifiers
			// (forall x0: ...)
			// and
			// (forall x1:...(forall x2: ...)...)
			// one after another, whereas we instantiate the inner quantifier
			// (forall x2: ...)
			// together with its outer quantifier
			// (forall x1: ...(forall x2: ...)...).

			// We instantiate each quantifier possibly multiple times with all the
			// combinations of concrete values for the quantified variables it contains, so
			// we will end up with multiple instantiated versions of the input formula.

			// Since we sequentially instantiate the quantifiers of the input formula, we
			// maintain partially instantiated input formulas in a list.
			List<String> partially_instantiated_input_formulas = new LinkedList<String>();
			partially_instantiated_input_formulas.add(quantified_input_formula.toString());
			for (Quantifier quantifier : quantified_input_formulas.get(quantified_input_formula)) {

				if (Thread.currentThread().isInterrupted()) {
					throw new Proof_Exception("Interrupted while making the assertions for the potential example");
				}

				List<String> instantiated_quantifiers = instantiate_quantifier(quantifier);
				List<String> further_instantiated_input_formulas = new LinkedList<String>();
				for (String instantiated_quantifier : instantiated_quantifiers) {
					for (String partially_instantiated_input_formula : partially_instantiated_input_formulas) {
						String further_instantiated_input_formula = String_Utility.substitute(
								partially_instantiated_input_formula, quantifier.toString(), instantiated_quantifier);
						further_instantiated_input_formulas.add(further_instantiated_input_formula);
					}
				}
				partially_instantiated_input_formulas = further_instantiated_input_formulas;
			}

			for (String instantiated_formula : partially_instantiated_input_formulas) {
				assert (!instantiated_formula.contains("forall"));
			}

			instantiated_formulas.addAll(partially_instantiated_input_formulas);
			for (Quant_Var quant_var : quant_vars) {
				if (quant_var.is_instantiated()) {
					List<Expr<?>> quant_var_constant_allocations = quant_var.make_expressions(context);
					constant_allocations.addAll(quant_var_constant_allocations);
					for (Expr<?> quant_var_constant_allocation : quant_var_constant_allocations) {
						if (quant_var_constant_allocation.isEq()) {
							Expr<?> constant = quant_var_constant_allocation.getArgs()[0];
							if (constant.getFuncDecl().getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED)) {
								constant_declarations.add(constant.getFuncDecl());
							}
						}
					}
					for (FuncDecl<?> further_declaration : quant_var.make_further_declarations()) {
						further_declarations.add(further_declaration);
					}
				}
			}
		}
	}

	// TLDR: Handles quantifier instantiations.
	// Replaces the quantified variables in the quantifier with combinations of
	// constants from possible_constants.
	// Also considers nested quantifiers.
	// Returns a list of instantiated quantifiers.
	private List<String> instantiate_quantifier(Quantifier quantifier) throws Proof_Exception {

		if (Thread.currentThread().isInterrupted()) {
			throw new Proof_Exception("Interrupted while instantiating the quantifiers");
		}

		// First, we want to get all the quantified variables that appear in the
		// quantifier.
		Symbol[] quantifier_variables = quantifier.getBoundVariableNames();
		int len = quantifier_variables.length;
		List<Expr<?>>[] quantifier_constants = new LinkedList[len];
		int number_of_values = 0;
		for (int i = 0; i < len; i++) {
			// Then, we get all the constants that correspond to each of the quantified
			// variables. There are multiple of them if we found multiple possible values
			// for the corresponding quantified variable.
			Quant_Var quant_var = names_to_quant_vars.get(quantifier_variables[i].toString());
			List<Expr<?>> constants = possible_constants.get(quant_var);
			if (number_of_values < constants.size()) {
				number_of_values = constants.size();
			}
			// Translate from De-Brujn indexing.
			quantifier_constants[len - i - 1] = constants;
			for (Expr<?> constant : constants) {
				FuncDecl<?> constant_declaration = constant.getFuncDecl();
				constant_declarations.add(constant_declaration);
			}
		}
		// By now, we have collected all the constants that we should instantiate our
		// quantifiers with. Example: If the quantifier has two quantified variables x0
		// and x1, and the proof contains the instantiations x0 = x00, x1 = x1, and x0 =
		// x01, x1 = x1,
		// then we instantiate the quantifier two times, once by replacing the
		// quantified variable x0 with the constant x00 and once by replacing it with
		// the constant x01, while we always replace the quantified variable x1 with the
		// constant x1.
		List<Expr<?>> instantiated_quantifiers = new LinkedList<Expr<?>>();
		for (int i = 0; i < number_of_values; i++) {
			Expr<?>[] current_constants = new Expr<?>[len];
			for (int j = 0; j < quantifier_constants.length; j++) {
				try {
					current_constants[j] = quantifier_constants[j].get(i);
				} catch (IndexOutOfBoundsException e) {
					// some variables have only one value (see x1 above)
					current_constants[j] = quantifier_constants[j].get(0);
				}
			}
			instantiated_quantifiers.add(quantifier.getBody().substituteVars(current_constants));
		}
		List<String> quantifierless_quantifiers = new LinkedList<String>();
		for (Expr<?> instantiated_quantifier : instantiated_quantifiers) {
			String quantifier_as_string = instantiated_quantifier.toString();

			// For each of our instantiated quantifiers, we also need to
			// instantiate nested quantifiers (if there are any).
			if (nested_quantifiers.contains(quantifier)) {
				List<String> instantiated_nested_quantifiers = instantiate_nested_quantifiers(instantiated_quantifier,
						quantifier_as_string);
				quantifierless_quantifiers.addAll(instantiated_nested_quantifiers);
			} else {
				// Otherwise, we just remember the initial instantiated quantifier.
				quantifierless_quantifiers.add(quantifier_as_string);
			}
		}
		return quantifierless_quantifiers;

	}

	// TLDR: Covers nested quantifiers.
	// Recursively traverses the instantiated_quantifier while looking for nested
	// quantifiers in the current_expression. Upon finding one, the nested
	// quantifier is too instantiated and each of the instantiated_sub_quantifiers
	// we find by doing so is used to replace the nested quantifier in the
	// instantiated_quantifier.
	private List<String> instantiate_nested_quantifiers(Expr<?> current_expression, String instantiated_quantifier)
			throws Proof_Exception {

		if (Thread.currentThread().isInterrupted()) {
			throw new Proof_Exception("Interrupted while instantiating nested quantifiers");
		}

		List<String> out = new LinkedList<String>();
		if (current_expression.isQuantifier()) {
			List<String> instantiated_sub_quantifiers = instantiate_quantifier((Quantifier) current_expression);
			for (String instantiated_sub_quantifier : instantiated_sub_quantifiers) {
				out.add(String_Utility.substitute(instantiated_quantifier, current_expression.toString(),
						instantiated_sub_quantifier));
			}
			return out;
		}
		if (current_expression.isApp()) {
			out.add(instantiated_quantifier);
			for (Expr<?> sub_expression : current_expression.getArgs()) {
				String sub_expression_as_string = sub_expression.toString();
				if (sub_expression_as_string.contains("forall")) {
					List<String> instantiated_sub_quantifiers = instantiate_nested_quantifiers(sub_expression,
							sub_expression.toString());
					List<String> new_out = new LinkedList<String>();
					for (String instantiated_sub_quantifier : instantiated_sub_quantifiers) {
						for (String candidate : out) {
							new_out.add(String_Utility.remove_let_and_substitute(candidate, sub_expression_as_string,
									instantiated_sub_quantifier));
						}
					}
					out = new_out;
				}
			}
		}
		return out;
	}

	// *****************************************************************************

	// *****************************************************************************
	// Minimization-related methods.

	// Removes all possible_values from all Quant_Var objects in quant_vars.
	public void clear_all_possible_values() {
		for (Quant_Var quant_var : quant_vars) {
			quant_var.clear_concrete_values();
		}
	}

	// Adds the value to each Quant_Var object in quant_vars whose corresponding
	// quantified variable was instantiated by the constant.
	public void re_add_possible_value(Expr<?> constant, Expr<?> value) {
		for (Quant_Var quant_var : possible_constants.keySet()) {
			if (possible_constants.get(quant_var).contains(constant)) {
				quant_var.add_concrete_value(value);
			}
		}
	}

	// *****************************************************************************

	// *****************************************************************************
	// Recovery-related methods.

	private void instantiate_with_default_value(Quant_Var quant_var) {
		quant_var.add_concrete_value(defaults.get_constant(context, quant_var.get_type()));
	}

	public void add_default_values() {
		for (Quant_Var quant_var : quant_vars) {
			if (!quant_var.is_explicitly_instantiated) {
				instantiate_with_default_value(quant_var);
			}
		}
	}

	// *****************************************************************************

	// *****************************************************************************
	// Pretty print methods.

	// Prints all Quant_Var objects in quant_vars with all the information we
	// collected so far to out.
	public void print_all_definitions(PrintStream out) {
		for (Quant_Var quant_var : quant_vars) {
			if (quant_var.is_vampire_quant_var()) {
				out.print(((Vampire_Quant_Var) quant_var).toString());
			} else {
				out.print(quant_var.print_definition());
			}
			out.println("******************************************");
		}
	}

	// Prints all Quant_Var objects in quant_vars that are instantiated so far
	// together with the possible value(s).
	public void print_all_instantiations(PrintStream out) {
		for (Quant_Var quant_var : quant_vars) {
			if (quant_var.is_instantiated()) {
				if (quant_var.is_vampire_quant_var()) {
					out.print(((Vampire_Quant_Var) quant_var).print_instantiation());
				} else {
					out.print(quant_var.print_instantiation());
				}
			}
		}
	}

	public String get_instantiations() {
		String out = "";
		int n_instantiations = 0;
		for (Quant_Var quant_var : quant_vars) {
			if (quant_var.is_instantiated()) {
				out += quant_var.get_name() + " = "
						+ String_Utility.remove_line_breaks(quant_var.concrete_values.toString()) + "\n";
				n_instantiations += quant_var.concrete_values.size();
			}
		}
		System.out.println("Number of instantiated quantifiers: " + n_instantiations);
		return out;
	}

	public String get_input_lines() {
		List<Expr<?>> input_lines = new LinkedList<Expr<?>>();
		for (Quant_Var quant_var : quant_vars) {
			if (quant_var.is_instantiated() && !input_lines.contains(quant_var.input_line)) {
				input_lines.add(quant_var.input_line);
			}
		}
		String out = "";
		for (Expr<?> input_line : input_lines) {
			out += String_Utility.remove_line_breaks(input_line.toString()) + "\n";
		}
		return out;
	}

	// *****************************************************************************

	// *****************************************************************************
	// E-Matching-related methods.

	public Set<String> create_triggering_terms(Set<Pattern_Wrapper> patterns) throws Proof_Exception {
		Set<String> dummies = new LinkedHashSet<String>();
		Set<String> triggering_terms = new LinkedHashSet<String>();

		for (Pattern_Wrapper pattern : patterns) {

			if (Thread.currentThread().isInterrupted()) {
				throw new Proof_Exception("Interrupted while creating the triggering terms");
			}

			Symbol[] vars = pattern.vars;
			if (vars.length == 0) {
				continue; // this pattern is not relevant for the contradiction
			}

			List<String> possible_triggering_terms = new LinkedList<String>();
			possible_triggering_terms.add(pattern.expr);

			for (Symbol aVar : vars) {
				String var_name = aVar.toString();
				Quant_Var quant_var = names_to_quant_vars.get(var_name);
				if (!quant_var.is_explicitly_instantiated) {
					instantiate_with_default_value(quant_var);
					Expr<?> additional_constant = quant_var.concrete_values.get(0);
					FuncDecl<Sort> additional_constant_decl = context.mkConstDecl(additional_constant.toString(),
							quant_var.get_type());
					dummies.add(additional_constant_decl.toString());
				}
				List<Expr<?>> concrete_values = quant_var.concrete_values;
				List<String> additional_triggering_terms = new LinkedList<String>();
				for (int val_index = 0; val_index < concrete_values.size(); val_index++) {
					for (int index = 0; index < possible_triggering_terms.size(); index++) {
						String possible_triggering_term = possible_triggering_terms.get(index);
						if (!possible_triggering_term.contains(var_name)) {
							additional_triggering_terms.add(possible_triggering_term);
							continue;
						}
						String concrete_val = concrete_values.get(val_index).toString();
						String new_triggering_term = String_Utility.substitute(possible_triggering_term, var_name,
								concrete_val);
						assert (!new_triggering_term.contains(":var"));
						additional_triggering_terms.add(new_triggering_term);
					}
				}
				possible_triggering_terms = additional_triggering_terms;
			}

			for (String triggering_term : possible_triggering_terms) {
				if (!triggering_terms.contains(triggering_term)) {
					triggering_terms.add(triggering_term);
					Sort range = pattern.range;
					String dummy_function_name = "dummy" + dummy_function_counter;
					FuncDecl<BoolSort> dummy_function_decl = context.mkFuncDecl(dummy_function_name, range,
							context.getBoolSort());
					dummies.add(dummy_function_decl.toString());
					dummy_function_counter += 1;
					dummies.add("(assert (" + dummy_function_name + " " + triggering_term + "))");
				}
			}
		}
		return dummies;
	}

// *****************************************************************************
}
