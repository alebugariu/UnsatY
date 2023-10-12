/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proof_analyser.unsat_core;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import util.Proof_Exception;
import util.String_Utility;
import util.Verbal_Output;
import util.Command_Line_Result;
import util.Command_Line_Utility;

public class Command_Line_Unsat_Core_Finder extends Unsat_Core_Finder {

	private BoolExpr[] unsat_core;

	public Command_Line_Unsat_Core_Finder(Context context) {
		super(context);
	}

	@Override
	public boolean is_unsat(File smt_file, Verbal_Output verbal_output) throws Proof_Exception {
		try {
			Scanner scanner = new Scanner(smt_file);
			String smt_file_name = String_Utility.get_file_name(smt_file);
			String tmp_file = "temp" + File.separator + smt_file_name + "_get_ucore.smt2";
			PrintStream output = new PrintStream(tmp_file);

			Map<String, String> assertions_map = new HashMap<String, String>();

			output.println("(set-option :produce-unsat-cores true)");
			while (scanner.hasNextLine()) {
				String line = scanner.nextLine();
				if (line.toLowerCase().equals("(set-option :smt.mbqi false)")) {
					// the benchmarks from the evaluation of the FM paper used E-matching, now we
					// need to enable MBQI
					output.println("(set-option :smt.mbqi true)");
				} else if (!line.contains("set-option :produce-proofs") && !line.contains("get-proof")) {
					output.println(line);
				}
				if (line.contains("assert")) {
					String name = String_Utility.get_name(line);
					assert (name != null);
					assertions_map.put(line, name);
				}
			}
			output.println("(get-unsat-core)");
			scanner.close();
			output.close();

			Command_Line_Result result = Command_Line_Utility.run_z3(new File(tmp_file));
			if (result.output.startsWith("unsat")) {
				String unsat_core_string = result.output.replace("unsat", "").trim();
				// remove the enclosing ()
				unsat_core_string = unsat_core_string.substring(1, unsat_core_string.length() - 1);
				List<String> assertion_names = Arrays.asList(unsat_core_string.split(" "));
				
				scanner = new Scanner(new File(tmp_file));
				String unsat_core_file = "temp" + File.separator + smt_file_name + "_unsat_core.smt2";
				output = new PrintStream(unsat_core_file);
				while (scanner.hasNextLine()) {
					String line = scanner.nextLine();
					if (line.contains("assert")) {
						String name = assertions_map.get(line);
						if(assertion_names.contains(name)) {  // is part of the unsat core
							output.println(line);
						}
					}
					else {
						output.println(line);
					}
				}
				scanner.close();
				output.close();
				
				unsat_core = context.parseSMTLIB2File(unsat_core_file, null, null, null, null);
				
				return true;
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		return false;
	}

	@Override
	public boolean is_unsat(BoolExpr[] formula, Verbal_Output verbal_output) throws Proof_Exception {
		String tmp_file = "temp" + File.separator + "get_ucore.smt2";
		Command_Line_Utility.write_formula_to_file(formula, context, "unsat", tmp_file);
		return is_unsat(new File(tmp_file), verbal_output);
	}

	@Override
	public BoolExpr[] get_unsat_core() {
		return unsat_core;
	}

}
