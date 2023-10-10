/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package evaluation;

import java.io.File;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;

import proofanalyser.Proof_Analyser_Framework.Prover;
import util.Proof_Exception;

public class Concurrency_Handler {

	public static Future<Void> process_file(ExecutorService executor, File file, Prover prover, String preprocessor)
			throws Proof_Exception {
		Benchmark_Runner runner = new Benchmark_Runner(file, prover, preprocessor);
		Future<Void> future = executor.submit(runner);
		return future;
	}
}
