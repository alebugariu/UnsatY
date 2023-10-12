/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proof_analyser.unsat_core;

import java.io.File;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import util.Proof_Exception;
import util.Verbal_Output;

public abstract class Unsat_Core_Finder {
	
	protected Context context;
	
	public Unsat_Core_Finder(Context context) {
		this.context = context;
	}
	
	public abstract boolean is_unsat(File smt_file, Verbal_Output verbal_output) throws Proof_Exception;
	
	public abstract boolean is_unsat(BoolExpr[] formula, Verbal_Output verbal_output) throws Proof_Exception;

	public abstract BoolExpr[] get_unsat_core();

}
