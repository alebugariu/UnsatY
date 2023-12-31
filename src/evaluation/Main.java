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
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.io.FileUtils;

import proof_analyser.Proof_Analyser_Framework.Prover;
import util.Command_Line_Utility;
import util.Proof_Exception;
import util.Setup;
import util.Verbal_Output.Log_Type;

public class Main {

	public static void main(String[] args) throws Proof_Exception, IOException {
		Options options = new Options();
		HelpFormatter formatter = new HelpFormatter();

		Option fileOpt = new Option("file", true, "absolute path to an smt file");
		options.addOption(fileOpt);

		Option folderOpt = new Option("folder", true, "absolute path to a folder with smt files");
		options.addOption(folderOpt);

		Option proverOpt = new Option("prover", true, "prover used to generate the unsat proof (Z3, Vampire)");
		proverOpt.setRequired(true);
		options.addOption(proverOpt);

		Option preprocessOpt = new Option("pre", true,
				"absolute path to the tool used to preprocess the inputs (transform them into NNF, ensure that all quantified variables have unique names, etc.)");
		options.addOption(preprocessOpt);

		Option ematchingOpt = new Option("ematching", false,
				"synthesize triggering terms for E-matching from the unsat proofs");
		options.addOption(ematchingOpt);

		CommandLineParser parser = new DefaultParser();
		CommandLine cmd = null;

		try {
			cmd = parser.parse(options, args);
		} catch (ParseException e) {
			formatter.printHelp("proof analyser help", options);
			System.exit(1);
		}

		String proverName = cmd.getOptionValue("prover").toLowerCase();

		Prover prover = null;
		if (proverName.equals("z3")) {
			prover = Prover.z3;
		} else if (proverName.equals("vampire")) {
			prover = Prover.vampire;
		} else {
			System.out.println("Unknown prover.");
			System.exit(1);
		}

		if (Setup.log_type == Log_Type.full) {
			File logsFolder = new File("logs");
			logsFolder.mkdir();
		}

		File tmpFolder = new File("temp");
		tmpFolder.mkdir();

		File outputFolder = new File("output");
		outputFolder.mkdir();

		String preprocessor = null;

		if (cmd.hasOption("pre")) {
			preprocessor = cmd.getOptionValue("pre");
		}

		Setup.E_MATCHING = cmd.hasOption("ematching");

		if (cmd.hasOption("folder")) {

			String folderName = cmd.getOptionValue("folder");
			File folder = new File(folderName);
			if (!folder.exists()) {
				System.out.println("The folder " + folderName + " does not exist!");
				System.exit(1);
			}
			if (!folder.isDirectory()) {
				System.out.println(folderName + " is not a folder!");
				System.exit(1);
			}
			Collection<File> files = FileUtils.listFiles(folder, new String[] { "smt2" }, true);
			evaluate(files, prover, preprocessor);
		}

		else if (cmd.hasOption("file")) {

			String fileName = cmd.getOptionValue("file");
			File file = new File(fileName);
			if (!file.exists()) {
				System.out.println("The file " + fileName + " does not exist!");
				System.exit(1);
			}
			if (!file.isFile()) {
				System.out.println(fileName + " is not a file!");
				System.exit(1);
			}
			Collection<File> files = new ArrayList<File>();
			files.add(file);
			evaluate(files, prover, preprocessor);
		}

		FileUtils.deleteDirectory(tmpFolder);
		assert (Command_Line_Utility.processes.size() == 0);
	}

	public static void evaluate(Collection<File> benchmarks, Prover prover, String preprocessor)
			throws Proof_Exception {
		int nr_threads = Runtime.getRuntime().availableProcessors();
		ExecutorService executor = Executors.newFixedThreadPool(nr_threads);
		Map<Future<Void>, File> threads_map = new HashMap<Future<Void>, File>();
		Statistics statistics = new Statistics(benchmarks.size());

		for (File benchmark : benchmarks) {
			threads_map.put(Concurrency_Handler.process_file(executor, benchmark, statistics, prover, preprocessor),
					benchmark);
		}
		for (Future<Void> future : threads_map.keySet()) {
			try {
				future.get(Setup.timeout, TimeUnit.MILLISECONDS);
			} catch (InterruptedException e) {
				File file = threads_map.get(future);
				System.out.println("Interrupted exception while processing the file " + file);
				e.printStackTrace();
			} catch (ExecutionException e) {
				File file = threads_map.get(future);
				System.out.println("Execution exception while processing the file " + file);
				e.printStackTrace();
			} catch (TimeoutException e) {
				if (!future.isDone()) {
					future.cancel(true);
				}
				File file = threads_map.get(future);
				System.out.println("Timeout reached while processing the file " + file);
				if (Setup.E_MATCHING || !Setup.API_unsat_core) {
					Command_Line_Utility.stop_processes(file);
				}
			}
		}
		executor.shutdown();
		statistics.print_summary();
	}
}