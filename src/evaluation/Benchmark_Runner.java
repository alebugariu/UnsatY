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

	public Benchmark_Runner(File input_file, Prover prover, Log_Type log_type) {
		this.input_file = input_file;
		this.prover = prover;
		this.log_type = log_type;
		set_printstream_to_new_file(input_file);
	}

	private void set_printstream_to_new_file(File input_file) {
		String file_name = String_Utility.get_file_name(input_file);
		file_name += "_benchmark_test_output_" + prover + ".txt";
		File file = new File("output" + File.separator + file_name);
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

	@Override
	public Void call() {
		Proof_Analyser_Framework framework = new Proof_Analyser_Framework(input_file, prover, log_type, log);
		try {
			framework.setup();
			framework.generate_proof();
			DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
			LocalDateTime now = LocalDateTime.now();
			System.out.println("Unsat proof sucessfully generated: " + dtf.format(now));
			if (framework.construct_potential_example()) {
				System.out.println("EXAMPLE CONSTRUCTRED SUCCESSFULLY.");
				framework.minimize_example();
				log.println("------------------------------------------");
				log.print(framework.get_user_presentation());
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
		} catch (Proof_Exception e) {
			System.out.println("FAIL: " + e.getMessage());
		}
		framework.close_context();
		return null;
	}
}