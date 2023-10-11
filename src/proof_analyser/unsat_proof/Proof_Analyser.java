/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package proof_analyser.unsat_proof;

import quant_var.Quant_Var_Handler;
import recovery.Proof_Concrete_Values;
import util.Proof_Exception;

/*
 * This interface allows us to use a generic Proof_Analyser in the other classes.
 */

public interface Proof_Analyser {
	
	public void generate_unsat_proof() throws Proof_Exception;

	// Uses a prover to generate an unsat-proof for the input.
	// Searches quantifier instantiations in there.
	// Throws a Proof_Exception if the prover cannot prove unsat within the
	// resources defined in the class Setup.
	// Returns a Quant_Var_Handler object that contains all the information
	// extracted from both the input and the unsat-proof.
	public Quant_Var_Handler extract_quantifier_instantiations() throws Proof_Exception;

	// Traverses the unsat-proof and collects all syntactically occurring
	// concrete values, which we can then consider as possible values for all
	// quantified variables of the same type.
	// Returns a Proof_Concrete_Values object that contains all these.
	// Assumes that the method prove has been called before.
	public Proof_Concrete_Values collect_concrete_values();

}