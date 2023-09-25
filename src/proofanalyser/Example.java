/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proofanalyser;

import java.io.File;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import quantvar.Quant_Var_Handler;
import util.Input_Compatibility;
import util.Proof_Exception;
import util.Verbal_Output;

/*
 * This class is used to construct a potential example.
 */

public class Example {

	// Takes care of printing results and intermediate steps.
	// Is provided in the constructor.
	private Verbal_Output verbal_output;

	// Contains all the information we need about the input.
	// Is provided in the constructor.
	private Input_Reader input_reader;

	// Contains all the information we need about the unsat-proof.
	// Is provided in the constructor.
	private Proof_Analyser proof_analyser;

	// "The main interaction with Z3 happens via the Context. It maintains all data
	// structures related to terms and formulas that are created relative to them."
	// - from the Z3 API.
	// Is provided in the constructor.
	private Context context;

	// Contains information about all quantified variables in the input as well as
	// whether and to which concrete values each of them is instantiated in the
	// unsat-proof examined by the proof_analyser.
	// Is provided in the constructor.
	private Quant_Var_Handler quant_vars;
	
	BoolExpr[] unsat_core;

	protected Example(Input_Reader input_reader, Proof_Analyser proof_analyser, Quant_Var_Handler quant_vars) {
		this.verbal_output = input_reader.verbal_output;
		this.input_reader = input_reader;
		this.proof_analyser = proof_analyser;
		this.context = input_reader.context;
		this.quant_vars = quant_vars;
	}

	// Contains the last example that we generated.
	private File example_file;
	
	public File get_File() {
		return example_file;
	}

	public String get_user_presentation(PrintStream output, Boolean success) {
		String out = "";
		if (!success) {
			out += "[I COULD NOT SUCCESSFULLY VALIDATE THE EXAMPLE. I PROVIDE YOU WHAT I DID FOR MANUAL INSPECTION]\n\n";
		}
		if (used_recovery) {
			out += "[I GENERATED THE FOLLOWING EXAMPLE WITH HELP OF RECOVERY METHODS. IT MAY THEREFORE NOT CORRESPOND TO THE UNSAT-PROOF]\n\n";
		}
		if (unsat_core != null) {
			out += "Instantiating the quantified variables:\n";
			out += quant_vars.get_instantiations();
			out += " leads to the following contradiction: \n";
			for (BoolExpr expression : unsat_core) {
				if (!(expression.isEq() && expression.getArgs()[0].isConst())) {
					// This is no assignment to a constant.
					out += expression.toString() + "\n";
				}
			}
			out += "\nThe following input formulas were instantiated:\n";
			out += quant_vars.get_input_lines();
		}
		return out;
	}

	// We use the methods and fields below to construct a potential example.

	/*
	 * For each quantified variable, we create as many constants as we have found
	 * possible concrete values. If we have not found any possible value, i.e. a
	 * quantified variable was probably not instantiated by the proof, then we still
	 * create a single associated constant. We need this for the case where this
	 * non-instantiated quantified variable occurs passively in a Quantifier, that
	 * is, it is syntactically present, but irrelevant for the contradiction. We
	 * then replace the quantified variables in all Quantifiers with combinations of
	 * those constants. These constants and expressions are created by quant_vars.
	 */

	// Generates a potential example and stores it at "temp\<name>.smt2"
	protected File make_new_example(String name) throws Proof_Exception {
		quant_vars.make_assertions(context);
		List<FuncDecl<?>> constant_declarations = quant_vars.constant_declarations;
		List<Expr<?>> constant_allocations = quant_vars.constant_allocations;
		List<Expr<?>> instantiated_formulas = quant_vars.instantiated_formulas;
		List<FuncDecl<?>> further_declarations = quant_vars.further_declarations;
		/*
		 * Example
		 * 
		 * If the input contains the following lines:
		 * 
		 * (declare-fun f (Int) Int)
		 * 
		 * (assert (forall ((x0 Int)) (=> (>= x0 0) (= (f x0) x0))))
		 * 
		 * (assert (forall ((x1 Int)) (> (f x1) 0))),
		 * 
		 * then the proof_analyser will find out that the unsat-proof instantiates the
		 * quantified variables x0 and x1 both with the concrete value 0. This means
		 * that the following declarations are added to our sets in make_new_example:
		 * 
		 * - constant_declarations: (declare-const x0 Int), (declare-const x1 Int).
		 * 
		 * - constant_allocations: (= x1 0), (= x0 0).
		 * 
		 * - quantifier_instantiations: (> (f x1) 0), (=> (>= x0 0) (= (f x0) x0)).
		 * 
		 * - further_declarations is empty since there are no more declarations needed.
		 */
		example_file = Input_Compatibility.make_example(input_reader.z3_input_file, verbal_output, name,
				constant_declarations, constant_allocations, instantiated_formulas, further_declarations);
		return example_file;
	}
	
	public Boolean is_the_same(BoolExpr[] other_example) {
		BoolExpr[] this_example = context.parseSMTLIB2File(example_file.getAbsolutePath(), null, null, null, null);
		if (this_example.length != other_example.length) {
			return false;
		}

		List<String> this_example_list = new LinkedList<String>();
		for (BoolExpr expression : this_example) {
			this_example_list.add(expression.toString());
		}
		List<String> other_example_list = new LinkedList<String>();
		for (BoolExpr expression : other_example) {
			other_example_list.add(expression.toString());
		}
		for (String expr : this_example_list) {
			if (!other_example_list.contains(expr)) {
				return false;
			}
		}
		for (String expr : other_example_list) {
			if (!this_example_list.contains(expr)) {
				return false;
			}
		}
		return true;
	}
	
	// *****************************************************************************
	// Recovery-related methods and fields.

	// Recovery flag that is used to warn the user when the content of the example
	// might not correspond to the unsat-proof.
	// Is set whenever we use one of the recovery strategies below.
	protected Boolean used_recovery = false;

	// Implements the recovery heuristic based on default values.
	protected void recovery_strategy_default_values() {
		quant_vars.add_default_values();
		used_recovery = true;
	}

	// Implements the recovery heuristic based on concrete values from the
	// unsat-proof. Considers these as potential values for all the quantified
	// variables of the same type for which we have not found explicit quantifier
	// instantiations in the unsat-proof.
	protected void recover_strategy_syntactically_appearing_concrete_values() {
		for (Expr<?> concrete_value : proof_analyser.collect_concrete_values().get()) {
			quant_vars.add_concrete_value(concrete_value);
		}
		used_recovery = true;
	}

	// Implements the recovery heuristic based on boundary testing.
	// Does not yet consider semantic constraints from the unsat-proof.
	protected void recover_strategy_off_by_one() {
		for (Expr<?> concrete_value : proof_analyser.collect_concrete_values().get()) {
			if (concrete_value.getSort().toString().equals("Int")) {
				Expr<?> concrete_value_plus_one = context.mkAdd((ArithExpr) concrete_value,
						(ArithExpr) context.mkInt(1));
				Expr<?> concrete_value_minus_one = context.mkSub((ArithExpr) concrete_value,
						(ArithExpr) context.mkInt(1));
				quant_vars.add_concrete_value(concrete_value_plus_one);
				quant_vars.add_concrete_value(concrete_value_minus_one);
			}
		}
		used_recovery = true;
	}
	
	// *****************************************************************************
}
