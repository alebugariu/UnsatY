/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

import com.microsoft.z3.Status;

import util.Verbal_Output.Log_Type;

public class Exception_Handler {

	// Prints the content of the buffer in verbal_output and then throws a
	// Proof_Exception with the error_message.
	public static void throw_proof_exception(String error_message, Verbal_Output verbal_output) throws Proof_Exception {
		if (Setup.log_type == Log_Type.full) {
			verbal_output.print_buffer();
		}
		throw new Proof_Exception(error_message);
	}

	// Prints the content of the buffer in verbal_output and then throws a
	// Proof_Exception with the error_message and the given status.
	public static void throw_proof_exception(String error_message, Verbal_Output verbal_output, Status status)
			throws Proof_Exception {
		if (Setup.log_type == Log_Type.full) {
			verbal_output.print_buffer();
		}
		throw new Proof_Exception(error_message, status);
	}

}
