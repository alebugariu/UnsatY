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
import java.util.Collection;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

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

		ExecutorService executor = Executors.newSingleThreadExecutor();
		
		File logsFolder = new File("logs");
		logsFolder.mkdir();
		
		File tmpFolder = new File("temp");
		tmpFolder.mkdir();
		
		File outputFolder = new File("output");
		outputFolder.mkdir();
		
		if (cmd.hasOption("folder")) {

			String folderName = cmd.getOptionValue("folder");
			File folder = new File(folderName);
			if (!folder.exists()) {
				System.out.println("The folder " + folderName + " does not exist!");
				System.exit(1);
			}
			Collection<File> files = FileUtils.listFiles(folder, new String[] { "smt2" }, true);
			for (File file : files) {
				Concurrency_Handler.process_file(executor, file, prover, Log_Type.full);
			}
			executor.shutdown();
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
			Concurrency_Handler.process_file(executor, file, prover, Log_Type.full);
			executor.shutdown();
			FileUtils.deleteDirectory(tmpFolder);
		}
	}
}