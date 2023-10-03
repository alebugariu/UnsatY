/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package evaluation;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.concurrent.Callable;

import proofanalyser.Proof_Analyser_Framework;
import proofanalyser.Proof_Analyser_Framework.Prover;
import util.Proof_Exception;
import util.String_Utility;
import util.Verbal_Output.Log_Type;

public class Benchmark_Runner implements Callable<Void> {

	private File input_file;
	private Prover prover;
	private PrintStream log;
	private Log_Type log_type;
	private String preprocessor;

	public Benchmark_Runner(File input_file, Prover prover, Log_Type log_type, String preprocessor)
			throws Proof_Exception {
		this.preprocessor = preprocessor;
		if (this.preprocessor == null) {
			this.input_file = input_file;
		} else {
			this.input_file = preprocess(input_file);
		}
		this.prover = prover;
		this.log_type = log_type;
		set_printstream_to_new_file(this.input_file);
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
		try {
			String preprocessing_script = preprocessor + File.separator + "src" + File.separator + "frontend"
					+ File.separator + "test_runner.py";
			Process python_process = new ProcessBuilder("python3", preprocessing_script, "PatternAugmenter",
					"--timeout", "600", "--location", file_path).start();

			BufferedReader stdError = new BufferedReader(new InputStreamReader(python_process.getErrorStream()));
			BufferedReader stdOutput = new BufferedReader(new InputStreamReader(python_process.getInputStream()));

			String error_message = "";
			String s;
			while ((s = stdError.readLine()) != null) {
				error_message += s + "\n";
			}
			if (!error_message.isEmpty()) {
				throw new Proof_Exception("Error during preprocessing: " + error_message);
			}

			String output = "";
			while ((s = stdOutput.readLine()) != null) {
				output += s + "\n";
			}
			if (output.contains("crash")) {
				throw new Proof_Exception("Error during preprocessing: " + output);
			}
			String new_file_path = file_path
					.replace(parent_folder, parent_folder + File.separator + "pattern_augmenter")
					.replace(file_name, file_name + "_std_unique_aug-gt_unsat-full");
			return new File(new_file_path);
		} catch (IOException e) {
			throw new Proof_Exception("Error during preprocessing: " + e.getMessage());
		}
	}

	public boolean preprocessing_enabled() {
		return preprocessor != null;
	}

	@Override
	public Void call() {
		Proof_Analyser_Framework framework = new Proof_Analyser_Framework(input_file, prover, log_type, log);
		try {
			DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
			LocalDateTime now = LocalDateTime.now();
			System.out.println("Started Calculations: " + dtf.format(now));
			framework.setup();
			framework.generate_proof();
			now = LocalDateTime.now();
			System.out.println("Unsat proof sucessfully generated: " + dtf.format(now));
			if (framework.construct_potential_example()) {
				System.out.println("EXAMPLE CONSTRUCTRED SUCCESSFULLY.");
				framework.minimize_example();
				log.println("------------------------------------------");
				log.print(framework.get_user_presentation());
				framework.minimize_input();
			} else {
				System.out.println("EXAMPLE CONSTURCTION FAILED.");
			}
			log.println("------------------------------------------");
			log.print("[STATUS: " + framework.get_status() + "]");
			log.print(", [MINIMIZATION: " + framework.get_minimization_success() + "]");
			log.println(", [RECOVERY: " + framework.get_recovery_info() + "].");
			System.out.print("[STATUS: " + framework.get_status() + "]");
			System.out.print(", [MINIMIZATION: " + framework.get_minimization_success() + "]");
			System.out.println(", [RECOVERY: " + framework.get_recovery_info() + "].");
			now = LocalDateTime.now();
			System.out.println("Finished Calculations: " + dtf.format(now));
			System.out.println();
		} catch (Proof_Exception e) {
			System.out.println("FAIL: " + e.getMessage());
		}
		framework.close_context();
		return null;
	}
}
