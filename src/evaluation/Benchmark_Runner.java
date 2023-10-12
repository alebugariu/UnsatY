/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package evaluation;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.concurrent.Callable;

import proof_analyser.Proof_Analyser_Framework;
import proof_analyser.Proof_Analyser_Framework.Prover;
import util.Command_Line_Result;
import util.Command_Line_Utility;
import util.Proof_Exception;
import util.Setup;
import util.String_Utility;
import util.Verbal_Output.Log_Type;

public class Benchmark_Runner implements Callable<Void> {

	private File input_file;
	private Prover prover;
	private PrintStream log;
	private String preprocessor;

	public Benchmark_Runner(File input_file, Prover prover, String preprocessor) throws Proof_Exception {
		this.preprocessor = preprocessor;
		if (this.preprocessor == null) {
			this.input_file = input_file;
		} else {
			this.input_file = preprocess(input_file);
		}
		this.prover = prover;
		if (Setup.log_type == Log_Type.full) {
			set_printstream_to_new_file(this.input_file);
		}
	}

	private void set_printstream_to_new_file(File input_file) {
		String file_name = String_Utility.get_file_name(input_file);
		file_name += "_benchmark_test_log_" + prover + ".txt";
		File file = new File("logs" + File.separator + file_name);
		try {
			if (!file.createNewFile()) {
				file.delete();
				file.createNewFile();
			}
			log = new PrintStream(file);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private File preprocess(File input_file) throws Proof_Exception {
		String file_name = String_Utility.get_file_name(input_file);
		String parent_folder = input_file.getParentFile().getName();
		String file_path = input_file.getAbsolutePath();
		System.out.println("Preprocessing " + file_name);
		String preprocessing_script = preprocessor + File.separator + "src" + File.separator + "frontend"
				+ File.separator + "test_runner.py";
		String[] process_args = new String[] { "python3", preprocessing_script, "--timeout", "600", "--location",
				file_path };
		Command_Line_Result result = Command_Line_Utility.run_process(process_args);

		if (!result.error.isEmpty()) {
			throw new Proof_Exception("Error during preprocessing: " + result.error);
		}

		if (result.output.contains("crash") && !result.output.contains("crashed in 0 cases")) {
			throw new Proof_Exception("Error during preprocessing: " + result.output);
		}
		String new_file_path = file_path.replace(parent_folder, parent_folder + File.separator + "pattern_augmenter")
				.replace(file_name, file_name + "_std_unique_aug-gt_unsat-full");
		return new File(new_file_path);
	}

	@Override
	public Void call() {
		Proof_Analyser_Framework framework = new Proof_Analyser_Framework(input_file, prover, log);
		try {
			System.out.println("Processing " + input_file.toString() + " with " + prover + ": ");
			DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
			LocalDateTime now = LocalDateTime.now();
			System.out.println("Started Calculations for " + input_file.toString() + ": " + dtf.format(now));
			framework.setup();
			if (framework.generate_unsat_core()) {
				framework.generate_proof();
				now = LocalDateTime.now();
				System.out.println(
						"Unsat proof sucessfully generated for " + input_file.toString() + ": " + dtf.format(now));
				if (framework.construct_potential_example()) {
					System.out.println("EXAMPLE CONSTRUCTRED SUCCESSFULLY for " + input_file.toString());
					framework.minimize_example();
					if (Setup.log_type == Log_Type.full) {
						log.println("------------------------------------------");
						log.print(framework.get_user_presentation());
					}
					framework.minimize_input();
				} else {
					System.out.println("EXAMPLE CONSTURCTION FAILED for " + input_file.toString());
				}
				if (Setup.log_type == Log_Type.full) {
					log.println("------------------------------------------");
					log.print("[MINIMIZATION: " + framework.get_minimization_success() + "]");
					log.println(", [RECOVERY: " + framework.get_recovery_info() + "].");
				}
				System.out.print("[MINIMIZATION: " + framework.get_minimization_success() + "]");
				System.out.println(", [RECOVERY: " + framework.get_recovery_info() + "].");
			} else {
				System.out.println("UNSAT CORE CONSTURCTION FAILED for " + input_file.toString());
			}
			now = LocalDateTime.now();
			System.out.println("Finished Calculations for " + input_file.toString() + ": " + dtf.format(now));
			System.out.println();
		} catch (Exception e) {
			String error_message = e.getMessage();
			System.out.println("FAIL for " + input_file.toString() + ": " + error_message);
			System.out.println();
		}
		framework.close_context();
		return null;
	}
}
