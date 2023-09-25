/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package recovery;

import java.util.HashSet;
import java.util.Set;

import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

/*
 * This class acts as a wrapper for collecting concrete values from an
 * unsat-proof.
 */

public class Proof_Concrete_Values {

	// Is initialized in the constructor.
	public Set<Expr<?>> concrete_values;

	public Set<Expr<?>> get() {
		return concrete_values;
	}

	public Proof_Concrete_Values() {
		concrete_values = new HashSet<Expr<?>>();
	}

	// Adds new_value to concrete_values if not already present.
	// Returns true if it was successfully added.
	public Boolean add(Expr<?> new_value) {
		new_value = new_value.simplify();
		if (!concrete_values.contains(new_value)) {
			concrete_values.add(new_value);
			return true;
		}
		return false;
	}

	// Returns the subset of concrete_values that have the sort type.
	public Set<Expr<?>> get(Sort type) {
		Set<Expr<?>> out = new HashSet<Expr<?>>();
		for (Expr<?> concrete_value : concrete_values) {
			try {
				if (concrete_value.getSort().equals(type)) {
					out.add(concrete_value);
				}
			} catch (Z3Exception e) {
				// It can happen that Z3 cannot determine the type of a concrete value and
				// therefore throws an Exception. We just ignore these.
			}
		}
		return out;
	}

	// Used for debugging.
	public void print() {
		System.out.println("Collected the following concrete values in the unsat-proof:");
		for (Expr<?> concrete_value : concrete_values) {
			System.out.println(concrete_value.toString());
		}
	}

}
