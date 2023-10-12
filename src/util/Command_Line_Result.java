/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

public class Command_Line_Result {

	public String error;
	public String output;

	public Command_Line_Result(String error, String output) {
		this.error = error;
		this.output = output;
	}

	@Override
	public String toString() {
		String as_string = "";
		if (!output.isEmpty()) {
			as_string += output;
		}
		if (!error.isEmpty()) {
			as_string += error;
		}
		return as_string;
	}
}