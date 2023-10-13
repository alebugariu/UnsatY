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
import java.util.List;
import java.util.Scanner;

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

	public boolean synthesisize_triggering_terms(File input_file, List<Expr<?>> patterns,
			Quant_Var_Handler quant_vars) throws Proof_Exception {

		File output_file = generate_triggering_terms(input_file, patterns, quant_vars);
		if (output_file == null) {
			return false;
		}
		return refuted_by_ematching(output_file);
	}

	private File generate_triggering_terms(File input_file, List<Expr<?>> patterns, Quant_Var_Handler quant_vars) throws Proof_Exception {
		try {
			String temp_file_path = "temp" + File.separator + FilenameUtils.getBaseName(input_file.getName())
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
			
			Scanner scanner = new Scanner(input_file);
			boolean first_assertion = true;
			while (scanner.hasNextLine()) {
				String line = scanner.nextLine();
				if(line.contains("assert") && first_assertion) {
					// add the additional declarations before the assertions
					for (FuncDecl<?> further_declaration : quant_vars.further_declarations) {
						output.println(further_declaration.toString());
						first_assertion = false;
					}
				}
				if (!line.contains("set-option") && !line.startsWith(";") && !line.contains("check-sat")
						&& !line.contains("get-proof") && !line.contains("(get-info :reason-unknown)")) {
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

	private boolean refuted_by_ematching(File file) throws Proof_Exception {
		Command_Line_Result result = Command_Line_Utility.run_z3(file);
		if(result.output.startsWith("unsat")) {
			return true;
		} 
		throw new Proof_Exception("E-matching returned: " + result + " for " + file);
	}
}