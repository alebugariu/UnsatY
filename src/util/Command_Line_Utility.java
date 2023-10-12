/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

public class Command_Line_Utility {

	public static Command_Line_Result run_z3(File file) {
		try {
			String file_name = file.getCanonicalPath();
			String[] process_args = new String[] { "z3", "-T:" + String.valueOf(Setup.z3_timout), file_name };
			return run_process(process_args);
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}

	public static Command_Line_Result run_process(String[] args) {
		try {
			Process process = new ProcessBuilder(args).start();

			BufferedReader stdError = new BufferedReader(new InputStreamReader(process.getErrorStream()));
			BufferedReader stdOutput = new BufferedReader(new InputStreamReader(process.getInputStream()));

			String error_message = "";
			String s;
			while ((s = stdError.readLine()) != null) {
				error_message += s + "\n";
			}

			String output = "";
			while ((s = stdOutput.readLine()) != null) {
				output += s + "\n";
			}
			return new Command_Line_Result(error_message, output);
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}

	public static void write_formula_to_file(BoolExpr[] formula, Context context, String status, String smt_file) {
		String formula_as_string = context.benchmarkToSMTString("", "", status, "", formula, context.mkBool(true));
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(smt_file, false);
			fileWriter.write(formula_as_string);
			fileWriter.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
