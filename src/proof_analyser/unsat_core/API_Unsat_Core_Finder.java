/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proof_analyser.unsat_core;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import util.Exception_Handler;
import util.Proof_Exception;
import util.Setup;
import util.Verbal_Output;

public class API_Unsat_Core_Finder implements Unsat_Core_Finder{

	private Context context;
	private Solver solver;

	public API_Unsat_Core_Finder(Context context) {
		this.context = context;
		// Enable unsat-core generation (which we did not need before) and disable proof
		// generation
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

	public BoolExpr[] get_unsat_core() {
		return solver.getUnsatCore();
	}

	private Status check(BoolExpr[] formula) {
		return solver.check(formula);
	}

	public String get_reason_unknown() {
		return solver.getReasonUnknown();
	}

	public Boolean is_unsat(BoolExpr[] formula, Verbal_Output verbal_output) throws Proof_Exception {
		// Note that we add the formula as an argument of the
		// check method rather than via solver.add(formula), because the
		// latter approach always produces empty unsat-cores.
		// See https://stackoverflow.com/questions/32595806/z3-java-api-get-unsat-core.
		Status status = check(formula);
		if (status.equals(Status.UNSATISFIABLE)) {
			verbal_output.add_to_buffer("[SUCCESS]", "Z3 returned unsat.");
			return true;
		} 
		if (status.equals(Status.SATISFIABLE)) {
			verbal_output.add_to_buffer("[PROBLEM]", "Z3 returned sat.");
			return false;
		}
		if (status.equals(Status.UNKNOWN)) {
			verbal_output.add_to_buffer("[PROBLEM]", "Z3 returned unknown.");
			Exception_Handler.throw_proof_exception("Z3 returned unknown because: " + get_reason_unknown(),
					verbal_output, Status.UNKNOWN);
			return false;
		}
		// Unreachable.
		return false;
	}

}
