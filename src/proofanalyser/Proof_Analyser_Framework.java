/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proofanalyser;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.List;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Status;

import quantvar.Quant_Var_Handler;
import util.Exception_Handler;
import util.Proof_Exception;
import util.String_Utility;
import util.Verbal_Output.Log_Type;

/*
 * This class provides an interface for the user.
 */

public class Proof_Analyser_Framework {

	// File containing the input.
	// Is provided in the constructor.
	private File input_file;

	// Controls the amount of additional output that is printed.
	// Can be set to none, reduced or full.
	// Is possibly provided in the constructor.
	// By default is set to none.
	private Log_Type log_type = Log_Type.none;

	// Indicates where the log should be printed.
	// Is possibly provided in the constructor.
	// By default uses System.out.
	PrintStream log = System.out;

	// Contains all the information we extract from the input.
	// Is null before the method setup has been called.
	private Input_Reader input_reader;

	// All the supported provers.
	public enum Prover {
		z3, vampire
	}

	// Indicator on what prover should be used.
	// Is possibly provided in the constructor.
	// By default uses Z3.
	private Prover prover = Prover.z3;

	// Contains all the information we extract from the unsat-proof.
	// Is null before the method prove has been called.
	private Proof_Analyser proof_analyser;

	private Quant_Var_Handler quant_vars;

	private Evaluator evaluator;
	private Example example;
	private File example_file;

	public Proof_Analyser_Framework(File input_file, Prover prover, Log_Type log_type, PrintStream log) {
		this.input_file = input_file;
		this.prover = prover;
		this.log_type = log_type;
		this.log = log;
	}

	// Sets up an Input_Reader object according to the default or the settings
	// provided in the constructor and returns a Proof_Analyser object.
	// Throws a Proof_Exception if it fails to parse the input or if the input does
	// not satisfy our assumptions:
	// - All quantified variables have unique names.
	// - There are no existential quantifiers.
	public void setup() throws Proof_Exception {
		this.input_reader = new Input_Reader(input_file, log_type, log);
		if (prover.equals(Prover.z3)) {
			// Set up a Z3_Proof_Analyser.
			input_reader.z3_setup();
			this.proof_analyser = new Z3_Proof_Analyser(input_reader);
		} else if (prover.equals(Prover.vampire)) {
			// Set up a Vampire_Proof_Analyser.
			input_reader.vampire_setup();
			input_reader.analyze_input();
			this.proof_analyser = new Vampire_Proof_Analyser(input_reader);
		} else {
			Exception_Handler.throw_proof_exception(
					"Unknown prover provided in the constructor of Proof_Analyser_Framework: " + prover + ".",
					input_reader.verbal_output);
		}
	}

	public void generate_proof() throws Proof_Exception {
		proof_analyser.generate_unsat_proof();
	}

	public Boolean construct_potential_example() throws Proof_Exception {
		this.quant_vars = proof_analyser.extract_quantifier_instantiations();
		this.example = new Example(input_reader, proof_analyser, quant_vars);
		String fileName = String_Utility.get_file_name(input_reader.get_initial_input_file());
		this.example_file = example.make_new_example(fileName + "_potential_example");
		this.evaluator = new Evaluator(input_reader, proof_analyser, quant_vars);
		success = evaluator.validate(example, example_file);
		return success;
	}

	public boolean generate_unsat_core() throws Proof_Exception {
		Context context = input_reader.context;
		Unsat_Core_Finder unsat_core_finder = new Unsat_Core_Finder(context);
		if (unsat_core_finder.is_unsat(input_reader.input, input_reader.verbal_output)) {
			BoolExpr[] unsat_core = unsat_core_finder.get_unsat_core();
			String unsat_core_assertions = input_reader.context.benchmarkToSMTString("", "", "unsat", "", unsat_core, context.mkBool(true));
			FileWriter fileWriter;
			try {
				fileWriter = new FileWriter(input_file, false);
				fileWriter.write(unsat_core_assertions);
				fileWriter.close();
				return true;
			} catch (IOException e) {
				e.printStackTrace();
				return false;
			} 
		}
		return false;
	}
	
	public File get_input_file() {
		return input_file;
	}

	private Boolean success = false;

	public Boolean recover_example() throws Proof_Exception {
		success = evaluator.recover(example, example_file);
		return success;
	}

	public Boolean minimize_example() throws Proof_Exception {
		success = evaluator.minimize(example);
		return success;
	}

	public Boolean minimize_input() {
		success = input_reader.minimize(example);
		return success;
	}

	public Status get_status() {
		return evaluator.status;
	}

	public Boolean get_minimization_success() {
		return evaluator.minimization;
	}

	public int get_recovery_info() {
		return evaluator.recovery;
	}

	public String get_user_presentation() {
		return example.get_user_presentation(log, success);
	}

	public void close_context() {
		input_reader.context.close();
	}

	// The method below are used to generate triggering terms for E-Matching.

	public List<Expr<?>> get_patterns() {
		return input_reader.get_patterns();
	}

	public Quant_Var_Handler get_quant_vars() {
		return input_reader.quant_vars;
	}

}