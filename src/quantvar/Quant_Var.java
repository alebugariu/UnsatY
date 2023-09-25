/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package quantvar;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_decl_kind;

import util.Proof_Exception;
import util.Setup;
import util.Vampire_Runner;
import util.Verbal_Output;

/*
 * This class is used to collect all the info about a quantified variable,
 * including its name and sort, the uninterpreted functions that use it as an
 * argument, possible values that it might be instantiated with and more.
 * 
 * It is easier to manage your set of Quant_Var objects using a
 * Quant_Var_Handler object.
 */

public class Quant_Var {

	// Takes care of printing results and intermediate steps.
	// Is provided in the constructor.
	private Verbal_Output verbal_output;

	// *****************************************************************************
	// Input-related methods and fields.

	// Name of this quantified variable in the input parsed by the Z3 API.
	// Is provided in the constructor.
	private Symbol name;
	// Example: x0.

	protected Symbol get_name() {
		return name;
	}

	// Sort of this quantified variable according to the Z3 API.
	// Is provided in the constructor.
	private Sort type;
	// Example: Int.

	protected Sort get_type() {
		return type;
	}

	// Input line where this quantified variable occurs according to the Z3 API.
	// Is provided in the constructor.
	protected Expr<?> input_line;

	protected int number_in_input_formula;

	// Quantifier that defines this quantified variable according to the Z3 API.
	// Is provided in the constructor.
	protected Quantifier quantifier;

	// If the quantifier that defines this quantified variable is nested in some
	// other Quantifier, then parent holds that other Quantifier.
	// Is provided in the constructor.
	// Can be null (if quantifier is not nested).
	protected Quantifier parent_quantifier;

	// Contains all applications of uninterpreted functions that use this quantified
	// variable as an argument.
	// Your Input_Reader and Proof_Analyser continuously add objects to this.
	protected Map<FuncDecl<?>, Set<Expr<?>>> function_applications_with_quantified_variables;

	public List<Expr<?>> get_function_applications() {
		List<Expr<?>> out = new LinkedList<Expr<?>>();
		for (Set<Expr<?>> applications : function_applications_with_quantified_variables.values()) {
			out.addAll(applications);
		}
		return out;
	}

	// This list holds all the possible concrete values that the unsat-proof
	// instantiates this quantified variable with.
	// Elements are continuously added by your Proof_Analyser object.
	protected List<Expr<?>> concrete_values;
	// Ideally, we find exactly one such possible value. However, it can happen that
	// we find multiple of them. Reasons for this are either unexpected behavior of
	// the prover or some over-approximation that might be done in your
	// Proof_Analyser object. We handle this undesired scenario by introducing
	// multiple copies of this quantified variable in the evaluation phase (more
	// information provided there).

	public Boolean is_explicitly_instantiated = false;

	// Constructor that creates a new Quant_Var object from scratch.
	// This constructor is called by your Input_Reader object.
	protected Quant_Var(Symbol name, Sort type, Expr<?> input_line, int number_in_input_formula, Quantifier quantifier,
			Quantifier parent_quantifier, Verbal_Output verbal_output) {
		this.verbal_output = verbal_output;
		this.name = name;
		this.type = type;
		this.input_line = input_line;
		this.number_in_input_formula = number_in_input_formula;
		this.quantifier = quantifier;
		this.parent_quantifier = parent_quantifier;
		this.function_applications_with_quantified_variables = new HashMap<FuncDecl<?>, Set<Expr<?>>>();
		this.concrete_values = new LinkedList<Expr<?>>();
	}

	public String toString() {
		return this.name.toString() + " = " + this.concrete_values.toString();
	}

	// *****************************************************************************

	// *****************************************************************************
	// Input-related methods.

	// Memorizes the application in function_applications_with_quantified_variables
	// if the name of this is equal to the variable (i.e., they have the same string
	// representation).
	protected void add_function_application_from_input(FuncDecl<?> f_decl, Expr<?> application, Expr<?> variable) {
		if (name.toString().equals(variable.toString())) {
			if (function_applications_with_quantified_variables.containsKey(f_decl)) {
				if (!function_applications_with_quantified_variables.get(f_decl).contains(application)) {
					function_applications_with_quantified_variables.get(f_decl).add(application);
				}
			} else {
				Set<Expr<?>> arguments = new HashSet<Expr<?>>();
				arguments.add(application);
				function_applications_with_quantified_variables.put(f_decl, arguments);
			}
		}
	}

	// Indicator whether there is a function called f_name that uses this quantified
	// variable as an argument.
	protected boolean contains_function_declaration(String f_name) {
		for (FuncDecl<?> f_decl : function_applications_with_quantified_variables.keySet()) {
			if (f_decl.getName().toString().equals(f_name)) {
				return true;
			}
		}
		return false;
	}

	// *****************************************************************************

	// *****************************************************************************
	// Proof-related methods.

	// Adds new_value to concrete_values if it is not already present.
	protected void add_concrete_value(Expr<?> new_value) {
		try {
			new_value = new_value.simplify();
			if (!concrete_values.contains(new_value)) {
				concrete_values.add(new_value);
			}
		} catch (Z3Exception e) {
			if (!Setup.testing_environment) {
				verbal_output.add_to_buffer("[PROBLEM]", "Tried to add the concrete value " + new_value
						+ " that has unknown type to the quantified variable " + name + ".");
			}
		}
	}

	// Indicator whether this quantified variable is instantiated in the
	// unsat-proof, i.e., whether we have found at least one concrete value.
	protected Boolean is_instantiated() {
		return !concrete_values.isEmpty();
	}

	// *****************************************************************************

	// *****************************************************************************
	// Evaluation-related methods.

	// Returns a non-empty list of unique constant declarations that we use to
	// represent this quantified variable in the evaluation phase.
	// Example: If this Quant_Var object refers to the quantified variable x0 and
	// there are three possible values, then we return the set {x00, x01, x02}.
	protected List<Expr<?>> make_constants(Context context) {
		List<Expr<?>> constants = new LinkedList<Expr<?>>();
		if (!is_instantiated() || concrete_values.size() == 1) {
			// If this quantified variable has not been instantiated, then we simply create
			// a single constant with the same name as the quantified variable. We need it
			// because it can occur "passively" in a quantifier that contributes to the
			// contradiction, that is, it is present in the quantifier but does not itself
			// contribute to the contradiction.
			constants.add(context.mkConst(name, type));
		} else {
			// If this quantified variable has been instantiated, we create a fresh unique
			// constant for each possible value. To prevent the name of such a constant from
			// being a substring of the name of another constant (which may later cause bugs
			// in combination with regex), we add leading 0's if necessary.
			int total_digits = get_num_digits(constants.size());
			for (int i = 0; i < concrete_values.size(); i++) {
				int current_digits = get_num_digits(i);
				String prefix = "";
				for (int j = 0; j < (total_digits - current_digits); j++) {
					prefix += "0";
				}
				// Finally, we can put the name together and create the constant.
				String new_name = name + "_inst" + prefix + String.valueOf(i);
				constants.add(context.mkConst(new_name, type));
			}
		}
		return constants;
	}

	// Returns the number of digits of x.
	private int get_num_digits(int x) {
		if (x < 10) {
			return 1;
		}
		return (get_num_digits(x % 10) + 1);
	}

	// If this quantified variable was instantiated in the unsat-proof, then we use
	// the Z3 API to assign every possible value that was found to one of the
	// constants returned by the make_constant method. We then return a map of
	// (name, assignment) pairs.
	// Example: If the name of this quantified variable is x0 and
	// concrete_values contains 0 and 1, then we return:
	// {("x00", x00 = 0),("x01", x01 = 1)}.
	// Returns null if concrete_values is empty.
	protected List<Expr<?>> make_expressions(Context context) {
		if (!is_instantiated()) {
			// If this quantified variable has never been instantiated, then we must not and
			// can not assign any value to it.
			return null;
		}
		List<Expr<?>> constants = make_constants(context);
		assert (constants.size() == concrete_values.size());
		List<Expr<?>> expressions = new LinkedList<Expr<?>>();
		for (int i = 0; i < constants.size(); i++) {
			Expr<Sort> constant = (Expr<Sort>) constants.get(i);
			Expr<Sort> value = (Expr<Sort>) concrete_values.get(i);
			expressions.add(context.mkEq(constant, value));
		}
		return expressions;
	}

	// Returns a list of declarations of uninterpreted functions and constants that
	// occur in the input_line.
	protected List<FuncDecl<?>> make_further_declarations() {
		// We need this since our values may include uninterpreted functions or
		// constants that are declared by/in the proof but do not appear in the input.
		List<FuncDecl<?>> declarations = new LinkedList<FuncDecl<?>>();
		// All uninterpreted functions that use this quantified variable as an argument
		// are already present in f_decls, no matter whether they have been defined in
		// the input or in the unsat-proof.
		for (FuncDecl<?> f_decl : function_applications_with_quantified_variables.keySet()) {
			if (input_line.toString().contains("(" + f_decl.getName().toString() + " ")) {
				declarations.add(f_decl);
			}
		}
		for (Expr<?> value : concrete_values) {
			// We find uninterpreted constants by directly looking at each value.
			possibly_add_declarations(value, declarations);
		}
		return declarations;
	}

	// Recursively adds the declarations of all constants that occur in expression
	// to declarations.
	private void possibly_add_declarations(Expr<?> expression, List<FuncDecl<?>> declarations) {
		if (expression.isConst() && expression.getFuncDecl().getDeclKind().equals(Z3_decl_kind.Z3_OP_UNINTERPRETED)) {
			// If the value is an uninterpreted constant, then we add its declaration (if
			// the entry is not already present).
			if (!declarations.contains(expression.getFuncDecl())) {
				declarations.add(expression.getFuncDecl());
			}
		}
		if (expression.isApp()) {
			// If the value is an application, then we recursively look at its arguments to
			// detect further constants.
			for (Expr<?> argument : expression.getArgs()) {
				possibly_add_declarations(argument, declarations);
			}
		}
	}

	// *****************************************************************************

	// *****************************************************************************
	// Minimization-related methods.

	// Removes all elements from concrete_values.
	protected void clear_concrete_values() {
		// We want to do that once we successfully evaluated an example, before
		// re-adding the possible values that are necessary according to the unsat-core.
		concrete_values.clear();
	}

	// *****************************************************************************

	// *****************************************************************************
	// Vampire-related methods and fields.

	// Constructor that creates a Quant_Var object on top of some other existing
	// Quant_Var object called parent by copying the contents of parent into this.
	// It can be used by subclasses of this that are adapted to some specific prover
	// but still rely on the information collected in the input_reader, like for
	// example the Vampire_Quant_Var.
	protected Quant_Var(Quant_Var parent) {
		this.verbal_output = parent.verbal_output;
		this.name = parent.get_name();
		this.type = parent.get_type();
		this.input_line = parent.input_line;
		this.quantifier = parent.quantifier;
		this.parent_quantifier = parent.parent_quantifier;
		this.function_applications_with_quantified_variables = parent.function_applications_with_quantified_variables;
		this.vampirized_input_line = parent.vampirized_input_line;
		// Note that we only copy the parts that were populated by the input_reader.
		this.concrete_values = new LinkedList<Expr<?>>();
	}

	// Indicator whether this Quant_Var object is actually a Vampire_Quant_Var
	// object. Returns true if this is a Vampire_Quant_Var object.
	protected Boolean is_vampire_quant_var() {
		// Since this is not the case, we just return false.
		return false;
	}

	// Translation of the input line where this quantified variable occurs
	// into syntax used in unsat-proofs generated by Vampire.
	// Is null before the method vampirize_quantifier has been called.
	protected String vampirized_input_line;

	// Initializes vampirized_quantifier (if not already done) and returns it.
	protected String vampirize_input_formula(File input_file, Set<String> names) throws Proof_Exception {
		if (this.vampirized_input_line == null) {
			this.vampirized_input_line = Vampire_Runner.translate_to_vampire(input_file, input_line, names,
					verbal_output);
			verbal_output.add_to_buffer("[INFO]", "Quant_Var " + get_name() + " vampirized the input line " + input_line
					+ ": " + vampirized_input_line + ".");
		}
		return vampirized_input_line;
	}

	// *****************************************************************************

	// *****************************************************************************
	// Pretty print methods.

	protected String print_definition() {
		String out = "[INFO] The quantified variable " + name + " of type " + type
				+ " was found in the following input line: \n";
		out += "\t" + input_line + ". \n";
		if (function_applications_with_quantified_variables.size() > 0) {
			out += "\t" + "It therefore appears with the following functions: \n";
			for (FuncDecl<?> f_decl : function_applications_with_quantified_variables.keySet()) {
				out += "\t" + f_decl + ": " + function_applications_with_quantified_variables.get(f_decl) + ". \n";
			}
		}
		return out;
	}

	protected String print_instantiation() {
		String out = "[INFO] Found the following possible instantiations for the quantified variable " + name + ": "
				+ concrete_values.toString() + ". \n";
		return out;
	}

	// *****************************************************************************
}