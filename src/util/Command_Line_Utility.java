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
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

public class Command_Line_Utility {

	public static Map<String, Process> processes = new ConcurrentHashMap<String, Process>();

	public static Command_Line_Result run_z3(File file) throws Proof_Exception {
		String file_name = file.getAbsolutePath();
		String[] process_args = new String[] { "z3", "-T:" + String.valueOf(Setup.z3_timout), file_name };
		return run_process(process_args, file.getName());
	}

	public static Command_Line_Result run_process(String[] args, String benchmark) throws Proof_Exception {
		try {
			Process process = new ProcessBuilder(args).start();
			processes.put(benchmark, process);

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

			processes.remove(benchmark);
			return new Command_Line_Result(error_message, output);
		} catch (IOException e) {
			throw new Proof_Exception(e.getMessage());
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
	
	private static void stop_process_with_name(String name) {
		Process process = processes.get(name);
		if (process != null) {
			process.destroy();
			processes.remove(name);
		}
	}

	public static void stop_processes(File benchmark) {
		String benchmark_name = String_Utility.get_file_name(benchmark);
		String ucore_file = benchmark_name + "_z3_input_get_ucore.smt2";
		String ematching_file = benchmark_name + "_z3_input_ematching.smt2";
		stop_process_with_name(ucore_file);
		stop_process_with_name(ematching_file);
	}

}
