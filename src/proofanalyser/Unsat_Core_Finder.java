/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proofanalyser;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import util.Setup;

public class Unsat_Core_Finder {

	private Context context;
	private Solver solver;

	public Unsat_Core_Finder(Context context) {
		this.context = context;
		// Enable unsat-core generation (which we did not need before) and disable proof generation
		this.context.updateParamValue("unsat_core", "true");
		this.context.updateParamValue("proof", "false");
		this.solver = this.context.mkSolver();
		// Set the solver settings.
		Params solver_settings = this.context.mkParams();
		solver_settings.add("auto-config", false);
		solver_settings.add("mbqi", true);
		solver_settings.add("ematching", false);
		solver_settings.add("unsat_core", true);
		solver_settings.add("timeout", Setup.z3_timout);
		solver_settings.add("max_memory", Setup.z3_memory_limit);
		this.solver.setParameters(solver_settings);
	}
	
	BoolExpr[] get_unsat_core() {
		return solver.getUnsatCore();
	}
	
	Status check(BoolExpr[] formula) {
		return solver.check(formula);
	}
	
	String get_reason_unknown() {
		return solver.getReasonUnknown();
	}

}
