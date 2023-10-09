/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import quantvar.Quant_Var_Handler;

/*
 * This class is used to take care of printing results and intermediate steps
 * across all stages of our proof analysis.
 */

public class Verbal_Output {

	// Indicator on the amount of additional output that is printed.
	// - none: Print nothing other than the final result.
	// - full: Print all intermediate steps. Information may be redundant.

	public enum Log_Type {
		none, full
	}

	// Indicates where the log should be printed.
	// Is possibly provided in the constructor.
	// By default uses System.out.
	private PrintStream log = System.out;

	// Contains intermediate steps that will be printed during the next call of any
	// print_... method. Is cleared after every call of a print_... method.
	private List<String> buffer;

	// Constructor if you want to print to System.out.
	public Verbal_Output() {
		this(System.out);
	}

	// Constructor if you want to print somewhere else.
	public Verbal_Output(PrintStream out) {
		this.log = out;
		buffer = new ArrayList<String>();
		if (Setup.log_type == Log_Type.full) {
			out.println("XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX");
		}
	}

	// Adds s to the buffer, prepended by the tag, if output_type is set to full.
	public void add_to_buffer(String tag, String s) {
		if (Setup.log_type == Log_Type.full) {
			buffer.add(tag + " " + s);
		} else if (tag.equals("[ERROR]")) {
			buffer.add(tag + " " + s);
		}
	}

	// Adds the string representation of all elements in objects to the buffer, each
	// prepended by the tag, if output_type is set to full.
	public void add_all_to_buffer(String tag, Object[] objects) {
		for (Object object : objects) {
			if (Setup.log_type == Log_Type.full) {
				add_to_buffer(tag, object.toString());
			} else if (tag.equals("[ERROR]")) {
				buffer.add(tag + " " + object);
			}
		}
	}

	// Prints the buffer before emptying it.
	public void print_buffer() {
		if (!buffer.isEmpty()) {
			log.println("------------------------------------------");
			for (String s : buffer) {
				log.println(s);
			}
			buffer.clear();
		}
	}

	// Prints information about all the quantified variables collected by an
	// Input_Reader object in quant_vars.
	public void print_input(File initial_input_file, Quant_Var_Handler quant_vars) {
		if (!buffer.isEmpty()) {
			print_buffer();
		}
		if (Setup.log_type == Log_Type.full) {
			log.println("------------------------------------------");
			log.println("[INFO] Set up our data structures as follows:");
			quant_vars.print_all_definitions(log);
		}
	}

	// Prints information about all the quantifier instantiations collected by a
	// Proof_Analyser object in quant_vars.
	public void print_prove(Quant_Var_Handler quant_vars) {
		if (!buffer.isEmpty()) {
			log.println("------------------------------------------");
			print_buffer();
		}
		log.println("------------------------------------------");
		if (Setup.log_type == Log_Type.full) {
			quant_vars.print_all_instantiations(log);
		}
	}

	// Prints information collected during a single evaluation run.
	public void print_evaluation_file_contents(File evaluation_file, List<String> declaration_print_buffer,
			List<String> assertion_print_buffer) {
		if (!buffer.isEmpty()) {
			log.println("------------------------------------------");
			print_buffer();
		}
		log.println("------------------------------------------");
		log.println("[INFO] Generated a potential example at " + evaluation_file.toString() + ".");
		log.println("[INFO] It has the following contents:");
		for (String line : declaration_print_buffer) {
			log.println("\t" + line);
		}
		for (String line : assertion_print_buffer) {
			log.println("\t" + line);
		}
	}

	// Prints the remaining elements in the print_buffer and that we succeeded.
	public void print_finish() {
		if (!buffer.isEmpty()) {
			log.println("------------------------------------------");
			print_buffer();
		}
		log.println("------------------------------------------");
		log.println("[SUCCESS] Evaluation success.");
	}
}