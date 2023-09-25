/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

import com.microsoft.z3.Status;

public class Proof_Exception extends Exception {

	private static final long serialVersionUID = -1660582443915549027L;
	private Status status;

	public Proof_Exception(String error_message) {
		super(error_message);
	}
	
	public Proof_Exception(String error_message, Status status) {
		super(error_message);
		this.status = status;
	}
	
	public Status getProofStatus() {
		return status;
	}
}
