/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package triggering_terms;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.LinkedHashSet;
import java.util.Scanner;
import java.util.Set;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;

import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

import quant_var.Quant_Var_Handler;
import util.Proof_Exception;
import util.Setup;
import util.Command_Line_Result;
import util.Command_Line_Utility;

/*
 * This class can be used to create triggering terms based on function
 * applications in patterns of the input formulas for E-Matching.
 * 
 * It works on top of the implementation of our technique for generating
 * examples.
 */

public class Triggering_Terms_Generator {

	public boolean synthesisize_triggering_terms(File input_file, Set<Expr<?>> patterns, Quant_Var_Handler quant_vars)
			throws Proof_Exception {

		File output_file = generate_ematching_file(input_file, patterns, quant_vars);
		if (output_file == null) {
			return false;
		}
		Command_Line_Result result = Command_Line_Utility.run_z3(output_file);
		result.output = result.output.replace("unsupported\n", "");
		if (result.output.startsWith("unsat")) {
			return true;
		}
		try {
			FileUtils.delete(output_file);
		} catch (IOException e) {
			e.printStackTrace();
		}
		throw new Proof_Exception("E-matching returned: " + result + " for " + output_file);
	}

	private File generate_ematching_file(File input_file, Set<Expr<?>> patterns, Quant_Var_Handler quant_vars)
			throws Proof_Exception {
		try {
			String temp_file_path = "output" + File.separator + FilenameUtils.getBaseName(input_file.getName())
					+ "_ematching.smt2";
			File temp_file = new File(temp_file_path);
			if (!temp_file.createNewFile()) {
				temp_file.delete();
				temp_file.createNewFile();
			}
			PrintStream output = new PrintStream(temp_file);
			output.println("(set-option :auto_config false)\n" + "(set-option :smt.mbqi false)");
			output.println("(set-option " + Setup.sat_random_seed + " " + Setup.get_sat_random_seed() + ")");
			output.println("(set-option " + Setup.smt_random_seed + " " + Setup.get_smt_random_seed() + ")");
			output.println("(set-option " + Setup.nlsat_seed + " " + Setup.get_nlsat_seed() + ")");

			Set<String> declarations = new LinkedHashSet<String>();

			Scanner scanner = new Scanner(input_file);
			boolean first_assertion = true;
			while (scanner.hasNextLine()) {
				String line = scanner.nextLine();
				if (line.contains("assert") && first_assertion) {
					// add the additional declarations before the assertions
					for (FuncDecl<?> further_declaration : quant_vars.further_declarations) {
						String declaration_str = further_declaration.toString();
						if (!declarations.contains(declaration_str)) {
							output.println(declaration_str);
						}
					}
					first_assertion = false;
				}
				if (!line.contains("set-option") && !line.startsWith(";") && !line.contains("check-sat")
						&& !line.contains("get-proof") && !line.contains("(get-info :reason-unknown)")) {
					if (line.contains("declare")) {
						declarations.add(line);
					}
					output.println(line);
				}
			}
			output.println();
			for (String triggering_term : quant_vars.create_triggering_terms(patterns)) {
				output.println(triggering_term);
			}
			output.println("(check-sat)");
			output.close();
			scanner.close();
			return temp_file;
		} catch (IOException e) {
			throw new Proof_Exception("Failed to generate the triggering terms because " + e.getMessage());
		}
	}
}