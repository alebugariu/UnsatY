/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package recovery;

import java.util.HashMap;
import java.util.Map;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

/*
 * This class contains static methods to retrieve default values used for
 * recovery (if our main approach failed).
 */

public class Default_Values {

	private static int constant_counter = 0;

	private static Map<Sort, Expr<?>> constants = new HashMap<Sort, Expr<?>>();

	// Uses the context to generate a constant of sort type.
	// We only have one constant per sort, because they might relate to each other.
	public static Expr<?> get_constant(Context context, Sort type) {
		if (!constants.containsKey(type)) {
			Expr<?> constant = context.mkFreshConst(("c_fresh_" + constant_counter++), type);
			constants.put(type, constant);
		}
		return constants.get(type);
	}

}