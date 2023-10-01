/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package evaluation;

import java.io.File;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import proofanalyser.Proof_Analyser_Framework.Prover;
import util.Verbal_Output.Log_Type;

public class Concurrency_Handler {

	public static void start_thread(ExecutorService executor, Benchmark_Runner runner)
			throws InterruptedException, ExecutionException {
		int timeout = 1200; // 600 s for the prover to generate the proof + 600 s for our tool to process it
		if (runner.preprocessing_enabled()) {
			timeout += 600; // additional 600s for preprocessing
		}
		DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy/MM/dd HH:mm:ss");
		LocalDateTime now = LocalDateTime.now();
		System.out.println("Started Calculations: " + dtf.format(now));
		// Kick off calculations.
		Future<Void> future = executor.submit(runner);
		try {
			future.get(timeout, TimeUnit.SECONDS);
		} catch (Exception e) {
			if (!future.isDone()) {
				future.cancel(true);
			}
		}
		now = LocalDateTime.now();
		System.out.println("Finished Calculations: " + dtf.format(now));
		System.out.println();
	}

	public static void process_file(ExecutorService executor, File file, Prover prover, Log_Type log_type, String preprocessor) {
		try {
			Benchmark_Runner runner = new Benchmark_Runner(file, prover, log_type, preprocessor);
			System.out.println("Processing " + file.toString() + " with " + prover + ": ");
			start_thread(executor, runner);
		} catch (Exception e) {
			System.out.println(e.getMessage());
		}
	}
}
