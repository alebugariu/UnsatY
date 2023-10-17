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
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

public class Command_Line_Utility {

	public static final String active_pids = "active_pids.txt";
	private static Map<Long, Process> processes = new HashMap<Long, Process>();

	public static Command_Line_Result run_z3(File file) throws Proof_Exception {
		String file_name = file.getAbsolutePath();
		String[] process_args = new String[] { "z3", "-T:" + String.valueOf(Setup.z3_timout), file_name };
		return run_process(process_args, file.getName());
	}

	public static Command_Line_Result run_process(String[] args, String benchmark) throws Proof_Exception {
		try {
			Process process = new ProcessBuilder(args).start();
			long pid = process.pid();
			processes.put(pid, process);
			add_pid(pid, benchmark);

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

			remove_pid(pid, benchmark);
			return new Command_Line_Result(error_message, output);
		} catch (IOException e) {
			throw new Proof_Exception(e.getMessage());
		}
	}

	private static synchronized void add_pid(long pid, String benchmark) throws IOException {
		String current_process = benchmark + " " + String.valueOf(pid) + System.lineSeparator();

		FileWriter writer = new FileWriter(active_pids, true);
		writer.write(current_process);
		writer.close();
	}

	private static synchronized void remove_pid(long pid, String benchmark) throws IOException {
		List<String> lines = Files.readAllLines(Paths.get(active_pids));
		String line_to_remove = benchmark + " " + String.valueOf(pid);
		lines.remove(line_to_remove);

		FileWriter writer = new FileWriter(active_pids, false);
		for (String line : lines) {
			writer.write(line + "\n");
		}
		writer.close();
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
	
	public static synchronized void stop_processes(File benchmark) {
		String benchmark_name = String_Utility.get_file_name(benchmark);
		String ucore_file = benchmark_name + "_z3_input_get_ucore.smt2";
		String ematching_file = benchmark_name + "_z3_input_ematching.smt2";
		try {
			List<String> lines = Files.readAllLines(Paths.get(active_pids));
			for (String line: lines) {
				String[] split_line = line.split(" ");
				String file_name = split_line[0];
				long pid = Long.valueOf(split_line[1]);
				if(file_name.equals(ucore_file) || file_name.equals(ematching_file)) {
					Process process = processes.get(pid);
					process.destroy();
					remove_pid(pid, ucore_file);
					remove_pid(pid, ematching_file);
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}

}
