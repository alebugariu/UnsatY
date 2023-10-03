/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package evaluation;

import java.io.File;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import proofanalyser.Proof_Analyser_Framework.Prover;
import util.Proof_Exception;
import util.Verbal_Output.Log_Type;

public class Concurrency_Handler {

	public static void start_thread(ExecutorService executor, Benchmark_Runner runner)
			throws InterruptedException, ExecutionException {
		int timeout = 1200; // 600 s for the prover to generate the proof + 600 s for our tool to process it
		// Kick off calculations.
		Future<Void> future = executor.submit(runner);
		try {
			future.get(timeout, TimeUnit.SECONDS);
		} catch (Exception e) {
			if (!future.isDone()) {
				future.cancel(true);
			}
		}
	}

	public static Future<Void> process_file(ExecutorService executor, File file, Prover prover, Log_Type log_type, String preprocessor) throws Proof_Exception{
			Benchmark_Runner runner = new Benchmark_Runner(file, prover, log_type, preprocessor);
			System.out.println("Processing " + file.toString() + " with " + prover + ": ");
			Future<Void> future = executor.submit(runner);
			return future;
	}
}
