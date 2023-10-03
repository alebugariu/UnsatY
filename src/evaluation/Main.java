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
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.io.FileUtils;

import proofanalyser.Proof_Analyser_Framework.Prover;
import util.Proof_Exception;
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

		File logsFolder = new File("logs");
		logsFolder.mkdir();

		File tmpFolder = new File("temp");
		tmpFolder.mkdir();

		File outputFolder = new File("output");
		outputFolder.mkdir();

		String preprocessor = null;

		if (cmd.hasOption("pre")) {
			preprocessor = cmd.getOptionValue("pre");
		}

		if (cmd.hasOption("folder")) {

			String folderName = cmd.getOptionValue("folder");
			File folder = new File(folderName);
			if (!folder.exists()) {
				System.out.println("The folder " + folderName + " does not exist!");
				System.exit(1);
			}
			Collection<File> files = FileUtils.listFiles(folder, new String[] { "smt2" }, true);
			evaluate(files, prover, preprocessor);
			FileUtils.deleteDirectory(tmpFolder);
			return;
		}

		if (cmd.hasOption("file")) {

			String fileName = cmd.getOptionValue("file");
			File file = new File(fileName);
			if (!file.exists()) {
				System.out.println("The file " + fileName + " does not exist!");
				System.exit(1);
			}
			Collection<File> files = new ArrayList<File>();
			files.add(file);
			evaluate(files, prover, preprocessor);
			FileUtils.deleteDirectory(tmpFolder);
		}
	}

	public static void evaluate(Collection<File> benchmarks, Prover prover, String preprocessor)
			throws Proof_Exception {
		int timeout = 1200; // 600 s for the prover to generate the proof + 600 s for our tool to process it
		int nr_threads = Runtime.getRuntime().availableProcessors();
		ExecutorService executor = Executors.newFixedThreadPool(nr_threads);
		List<Future<Void>> threads = new ArrayList<Future<Void>>();

		for (File benchmark : benchmarks) {
			threads.add(Concurrency_Handler.process_file(executor, benchmark, prover, Log_Type.full, preprocessor));
		}
		for (Future<Void> future : threads) {
			try {
				future.get(timeout, TimeUnit.SECONDS);
			} catch (Exception e) {
				if (!future.isDone()) {
					future.cancel(true);
				}
			}
		}
		executor.shutdown();
	}
}