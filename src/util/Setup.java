/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

public class Setup {
	public static int z3_timout = 600000; // 600 s in ms.
	public static int z3_memory_limit = 6000; // 6000 MB.
	public static int z3_rlimit = 10000000;

	public static String vampire_timeout = "600"; // 600 s.
	public static String vampire_memory_limit = "6000"; // 6000 MB.

	private static String sat_random_seed_value = "488";
	private static String smt_random_seed_value = "599";
	private static String nlsat_seed_value = "611";

	public static final String sat_random_seed = ":sat.random_seed";
	public static final String smt_random_seed = ":smt.random_seed";
	public static final String nlsat_seed = ":nlsat.seed";

	// Returns the current value of sat_random_seed and restores it to the default.
	public static String get_sat_random_seed() {
		String seed = sat_random_seed_value;
		sat_random_seed_value = "488";
		return seed;
	}

	// Returns the current value of smt_random_seed and restores it to the default.
	public static String get_smt_random_seed() {
		String seed = smt_random_seed_value;
		smt_random_seed_value = "599";
		return seed;
	}

	// Returns the current value of nlsat_seed and restores it to the default.
	public static String get_nlsat_seed() {
		String seed = nlsat_seed_value;
		nlsat_seed_value = "611";
		return seed;
	}

	// Sets the sat_random_seed to seed.
	public static void set_sat_random_seed(String seed) {
		sat_random_seed_value = seed;
	}

	// Sets the smt_random_seed to seed.
	public static void set_smt_random_seed(String seed) {
		smt_random_seed_value = seed;
	}

	// Sets the nlsat_seed to seed.
	public static void set_nlsat_seed(String seed) {
		nlsat_seed_value = seed;
	}

	public static Boolean testing_environment = false;

}
