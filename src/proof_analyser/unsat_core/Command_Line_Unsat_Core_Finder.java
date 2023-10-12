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
			String tmp_file = "temp" + File.separator + String_Utility.get_file_name(smt_file) + "_get_ucore.smt2";
			PrintStream output = new PrintStream(tmp_file);

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
			}
			output.println("(get-unsat-core)");
			scanner.close();
			output.close();

			Command_Line_Result result = Command_Line_Utility.run_z3(new File(tmp_file));
			if (result.output.startsWith("unsat")) {
				String unsat_core_string = result.output.replace("unsat", "").trim();
				unsat_core_string = unsat_core_string.substring(1, unsat_core_string.length() - 1); // remove the enclosing ()
				String[] assertion_names = unsat_core_string.split(" ");
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
