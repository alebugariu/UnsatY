/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package triggering_terms;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.List;
import java.util.Scanner;

import org.apache.commons.io.FilenameUtils;

import com.microsoft.z3.Expr;

import proof_analyser.Proof_Analyser_Framework;
import proof_analyser.Proof_Analyser_Framework.Prover;
import quant_var.Quant_Var_Handler;
import util.Proof_Exception;
import util.Setup;

/*
 * This class can be used to create triggering terms based on function
 * applications in patterns of the input formulas for E-Matching.
 * 
 * It works on top of the implementation of our technique for generating
 * examples.
 */

public class Triggering_Terms_Generator {

	private static String base_path = "test" + File.separator + "files";

	public static void main(String[] args) throws Proof_Exception, IOException {
		if (args.length != 3) {
			System.out.println("Please provide the input file/folder, the prover [Z3, Vampire], and the path to Z3!");
			return;
		}

		String file_name = args[0];
		File input = new File(base_path + File.separator + file_name);
		if (!input.exists()) {
			System.out.println("Invalid file/folder name: " + base_path + File.separator + file_name);
			return;
		}

		String prover_name = args[1];
		Prover prover = null;
		if (prover_name.toLowerCase().equals("z3")) {
			prover = Prover.z3;
		} else if (prover_name.toLowerCase().equals("vampire")) {
			prover = Prover.vampire;
		} else {
			System.out.println("Invalid prover: " + prover_name);
			return;
		}

		String z3_path = args[2];
		if (input.isDirectory()) {
			for (File input_file : input.listFiles()) {
				construct_triggering_terms_from_proof(input_file, prover, z3_path);
			}
		} else {
			construct_triggering_terms_from_proof(input, prover, z3_path);
		}

	}

	private static void construct_triggering_terms_from_proof(File input_file, Prover prover, String z3_path)
			throws Proof_Exception, IOException {
		Proof_Analyser_Framework framework = new Proof_Analyser_Framework(input_file, prover, System.out);
		framework.setup();
		framework.generate_proof();
		boolean success = framework.construct_potential_example();
		if (!success) {
			System.out.println("We were not able to construct an example from the proof");
			return;
		}

		// Note: we do not minimize the example, since the minimization with MBQI may
		// remove values for some quantified variables which are relevant for E-matching

		List<Expr<?>> pattern_function_applications = framework.get_patterns();
		File output_file = generate_triggering_terms(input_file, pattern_function_applications,
				framework.get_quant_vars());
		if (output_file == null) {
			System.out.println("We were not able to generate the triggering terms");
			return;
		}

		run_ematching(output_file, z3_path);
	}

	private static File generate_triggering_terms(File input_file, List<Expr<?>> pattern_function_applications,
			Quant_Var_Handler quant_vars) {
		try {
			String temp_file_path = "temp" + File.separator + FilenameUtils.getBaseName(input_file.getName())
					+ "_ematching.smt2";
			File temp_file = new File(temp_file_path);
			if (!temp_file.createNewFile()) {
				temp_file.delete();
				temp_file.createNewFile();
			}
			PrintStream output = new PrintStream(temp_file);
			output.println("(set-option :AUTO_CONFIG false)\n" + "(set-option :smt.MBQI false)");
			output.println("(set-option " + Setup.sat_random_seed + " " + Setup.get_sat_random_seed() + ")");
			output.println("(set-option " + Setup.smt_random_seed + " " + Setup.get_smt_random_seed() + ")");
			output.println("(set-option " + Setup.nlsat_seed + " " + Setup.get_nlsat_seed() + ")");
			Scanner scanner = new Scanner(input_file);
			while (scanner.hasNextLine()) {
				String line = scanner.nextLine();
				if (!line.contains("set-option") && !line.startsWith(";") && !line.contains("check-sat")
						&& !line.contains("get-proof") && !line.contains("(get-info :reason-unknown)")) {
					output.println(line);
				}
			}
			output.println();
			for (String triggering_term : quant_vars.create_triggering_terms(pattern_function_applications)) {
				output.println(triggering_term);
			}
			output.println("(check-sat)");
			output.close();
			scanner.close();
			return temp_file;
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}

	private static void run_ematching(File file, String z3_path) {
		try {
			String file_name = file.getCanonicalPath();
			String command = z3_path + "z3 " + file_name;
			Process z3Process = Runtime.getRuntime().exec(command);
			BufferedReader output = new BufferedReader(new InputStreamReader(z3Process.getInputStream()));
			String result = "";
			String line = output.readLine();
			while (line != null) {
				result += line + "\n";
				line = output.readLine();
			}
			if (result.startsWith("unsat")) {
				System.out.println(file_name + " refuted via E-matching!");
			} else {
				System.out.println("E-matching returned: " + result + " for " + file_name);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}