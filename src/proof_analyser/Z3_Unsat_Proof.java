/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proof_analyser;

import com.microsoft.z3.Expr;

public class Z3_Unsat_Proof extends Unsat_Proof {
	
	private Expr<?> proof;
	
	public Z3_Unsat_Proof(Expr<?> proof) {
		this.proof = proof;
	}

	public Expr<?> getProofExpression(){
		return proof;
	}
}
