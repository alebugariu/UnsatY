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
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import quantvar.Quant_Var_Handler;
import util.Exception_Handler;
import util.Proof_Exception;
import util.Setup;
import util.String_Utility;
import util.Verbal_Output;

/*
 * This class is used to check whether a potential example is unsat.
 *
 * Regardless of which prover was used for generating the unsat-proof, we use
 * the Z3 API for that, since it is more reliable (than using Vampire via
 * command-line) and can produce unsat-cores (which Vampire cannot). Since the
 * potential examples are quantifier-free, checking for unsat is expected to be
 * fast.
 * 
 * If the example is unsat (evaluation success), then we attempt to minimize it
 * with unsat-core information. No matter whether the minimization succeeds or
 * not, we return a successfully validated example.
 * 
 * If the example is sat (evaluation failure), then we use recovery approaches
 * to find further possible concrete values and try again. If we unsuccessfully
 * tried all recovery approaches, then we return the most recently generated
 * potential (partial) example while mentioning that it did not successfully
 * validate as we did not find the necessary concrete values to instantiate the
 * quantified variables with.
 * 
 * If the example is unknown (evaluation failure), then we return the potential
 * (partial) example while mentioning that it did not successfully validate due
 * to an error with the prover.
 * 
 * Objects of this class should be created by a Proof_Analyser object so that
 * the arguments of the constructor are set appropriately.
 */

public class Evaluator {

	// Takes care of printing results and intermediate steps.
	// Is provided in the constructor.
	private Verbal_Output verbal_output;

	// "The main interaction with Z3 happens via the Context. It maintains all data
	// structures related to terms and formulas that are created relative to them."
	// - from the Z3 API.
	// Is provided in the constructor.
	private Context context;

	// The solver that we use for evaluation.
	// Is initialized in the constructor.
	private Solver evaluation_solver;

	private BoolExpr true_expression;

	// Expects a Quant_Var_Handler object that is populated appropriately.
	// Do not call this constructor yourself but use the evaluate method in your
	// Proof_Analyser object.
	protected Evaluator(Input_Reader input_reader, Proof_Analyser proof_analyser, Quant_Var_Handler quant_vars) {
		this.verbal_output = input_reader.verbal_output;
		this.context = input_reader.context;
		// Enable unsat-core generation (which we did not need before).
		context.updateParamValue("unsat_core", "true");
		this.evaluation_solver = context.mkSolver();
		// Set the solver settings.
		Params evaluation_solver_settings = context.mkParams();
		evaluation_solver_settings.add("auto-config", false);
		evaluation_solver_settings.add("mbqi", true);
		evaluation_solver_settings.add("ematching", false);
		evaluation_solver_settings.add("unsat_core", true);
		evaluation_solver_settings.add("timeout", Setup.z3_timout);
		evaluation_solver_settings.add("max_memory", Setup.z3_memory_limit);
		evaluation_solver.setParameters(evaluation_solver_settings);
		this.true_expression = this.context.mkBool(true);
	}

	protected Status status = Status.SATISFIABLE;
	protected Boolean minimization;
	protected int recovery;

	protected Boolean validate(Example example, File example_file) {
		BoolExpr[] parsed_example = context.parseSMTLIB2File(example_file.getAbsolutePath(), null, null, null, null);
		try {
			if (is_unsat(parsed_example)) {
				return true;
			}
		} catch (Proof_Exception e) {
			return false;
		}
		// Unreachable.
		return false;
	}

	// Tries to apply different recovery approaches.
	// Returns true upon success (i.e., when the constructed example is unsat).
	protected Boolean recover(Example example, File example_file) {
		recovery = 0;
		try {
			if (Setup.testing_environment) {
				DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
				LocalDateTime now = LocalDateTime.now();
				System.out.println("Started Recovery 1: " + dtf.format(now));
			}
			example.recovery_strategy_default_values();
			example_file = example.make_new_example("potential_example_recover_1");
			recovery = 1;
			BoolExpr[] parsed_potential_example = context.parseSMTLIB2File(example_file.getAbsolutePath(), null, null,
					null, null);
			if (!is_unsat(parsed_potential_example)) {
				if (Setup.testing_environment) {
					DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
					LocalDateTime now = LocalDateTime.now();
					System.out.println("Started Recovery 2: " + dtf.format(now));
				}
				example.recover_strategy_syntactically_appearing_concrete_values();
				example_file = example.make_new_example("potential_example_recover_2");
				recovery = 2;
				parsed_potential_example = context.parseSMTLIB2File(example_file.getAbsolutePath(), null, null, null,
						null);
				if (!is_unsat(parsed_potential_example)) {
					if (Setup.testing_environment) {
						DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
						LocalDateTime now = LocalDateTime.now();
						System.out.println("Started Recovery 3: " + dtf.format(now));
					}
					example.recover_strategy_off_by_one();
					example_file = example.make_new_example("potential_example_recover_3");
					recovery = 3;
					parsed_potential_example = context.parseSMTLIB2File(example_file.getAbsolutePath(), null, null,
							null, null);
					if (!is_unsat(parsed_potential_example)) {
						return false;
					}
				}
			}
		} catch (Proof_Exception e) {
			return false;
		}
		return true;
	}

	// Tries to minimize a successfully validated potential example.
	protected boolean minimize(Example example) throws Proof_Exception {
		minimization = false;

		BoolExpr[] unsat_core = evaluation_solver.getUnsatCore();

		if (unsat_core.length > 0 && !Setup.testing_environment) {
			verbal_output.add_to_buffer("[INFO]", "Z3 generates the following UNSAT-core:");
			verbal_output.add_all_to_buffer("\t", unsat_core);
		}

		example.unsat_core = unsat_core;
		String minimized_example = context.benchmarkToSMTString("", "", "unsat", "", unsat_core, true_expression);
		String minimized_example_name = String_Utility.get_file_name(example.get_File()) + "_minimized.smt2";

		String temp_file_path = "temp" + File.separator + minimized_example_name;
		try {
			File temp_file = new File(temp_file_path);
			if (!temp_file.createNewFile()) {
				temp_file.delete();
				temp_file.createNewFile();
			}
			PrintStream output = new PrintStream(temp_file);
			output.println(minimized_example);
			output.close();
		} catch (Exception e) {
			if (!Setup.testing_environment) {
				verbal_output.add_to_buffer("[INFO]", e.getMessage());
				verbal_output.add_all_to_buffer("\t", e.getStackTrace());
			}
			Exception_Handler.throw_proof_exception("Failed to write the minimized example to file.", verbal_output);
		}

		if (!example.is_the_same(unsat_core)) {
			// Success.
			minimization = true;
			return true;
		}
		// Minimization fail.
		status = Status.UNSATISFIABLE;
		return true;
	}

	// Checks with Z3 whether the potential_example is unsat.
	// Returns true if that is the case
	private Boolean is_unsat(BoolExpr[] potential_example) throws Proof_Exception {
		// Note that we add the evaluation_program as an argument of the
		// check method rather than via solver.add(evaluation_program), because the
		// latter approach always produces empty unsat-cores.
		// See https://stackoverflow.com/questions/32595806/z3-java-api-get-unsat-core.
		status = evaluation_solver.check(potential_example);
		if (status.equals(Status.UNSATISFIABLE)) {
			verbal_output.add_to_buffer("[SUCCESS]", "The potential example is unsat.");
			return true;
		} else if (status.equals(Status.SATISFIABLE)) {
			verbal_output.add_to_buffer("[PROBLEM]", "The potential example is sat.");
			verbal_output.add_to_buffer("[PROBLEM]", "It therefore does not suffice to produce the contradiction.");
			return false;
		} else if (status.equals(Status.UNKNOWN)) {
			verbal_output.add_to_buffer("[PROBLEM]", "The potential example is unknown.");
			verbal_output.add_to_buffer("[PROBLEM]", "It therefore does not suffice to produce the contradiction.");
			Exception_Handler.throw_proof_exception(
					"The potential example is unknown: " + evaluation_solver.getReasonUnknown(), verbal_output,
					Status.UNKNOWN);
		}
		// Unreachable.
		return false;
	}
}