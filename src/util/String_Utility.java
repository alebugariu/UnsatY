/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;

import util.wrapper.Let_Wrapper;

/*
 * This class contains a collection of static regex and other string-based
 * methods that are used at multiple stages in this project. For each of these,
 * there are a few tests in Benchmark_Test that basically serve as a
 * specification for how the method should behave.
 */

public class String_Utility {

	public static String get_file_name(File file) {
		String nameWithExtension = file.getName();
		return nameWithExtension.substring(0, nameWithExtension.indexOf(".smt2"));
	}

	// *****************************************************************************
	// Basic regex methods.

	// Escapes all metacharacters in source, which are characters that are
	// interpreted by regex to have special meanings. We prepend them by "\\".
	public static String escape_metacharacters(String source) {
		String[] metacharacters = { "<", ">", "(", ")", "[", "]", "{", "}", "^", "-", "=", "$", "!", "|", "?", "*", "+",
				".", ";" };
		// We need to handle the character '\' separately before adding it in front of
		// any other metacharacters.
		source.replace("\\", "\\\\");
		for (String metacharacter : metacharacters) {
			source = source.replace(metacharacter, "\\" + metacharacter);
		}
		return source;
	}

	// Returns the first match of regex in source.
	// Throws a Proof_Exception if regex matches nowhere in source.
	public static String match_first(String regex, String source) throws Proof_Exception {
		Pattern pattern = Pattern.compile(regex);
		Matcher matcher = pattern.matcher(source);
		if (matcher.find()) {
			return matcher.group();
		} else {
			throw new Proof_Exception(regex + " matches nowhere in " + source + ".");
		}
	}

	// Returns the last match of regex in source.
	// Throws a Proof_Exception if regex matches nowhere in source.
	public static String match_last(String regex, String source) throws Proof_Exception {
		Pattern pattern = Pattern.compile(regex);
		Matcher matcher = pattern.matcher(source);
		String out = "";
		while (matcher.find()) {
			out = matcher.group();
		}
		if (out.equals("")) {
			throw new Proof_Exception(regex + " matches nowhere in " + source + ".");
		}
		return out;
	}

	// Returns a list of all matches of regex in source.
	// Returns null if regex matches nowhere in source.
	public static List<String> match_all(String regex, String source) {
		Pattern pattern = Pattern.compile(regex);
		Matcher matcher = pattern.matcher(source);
		LinkedList<String> matches = new LinkedList<String>();
		while (matcher.find()) {
			matches.add(matcher.group());
		}
		return matches;
	}

	// Replaces the first match of regex in source by replace_by.
	public static String replace_first(String regex, String source, String replace_by) {
		Pattern pattern = Pattern.compile(regex);
		Matcher matcher = pattern.matcher(source);
		return matcher.replaceFirst(escape_metacharacters(replace_by));
	}

	// Replaces each match of regex in source by replace_by.
	public static String replace_all(String regex, String source, String replace_by) {
		Pattern pattern = Pattern.compile(regex);
		Matcher matcher = pattern.matcher(source);
		source = matcher.replaceAll(escape_metacharacters(replace_by));
		return source;
	}

	// Replaces each match of regex in source that has should_contain as a substring
	// by replace_by.
	public static String replace_all_if(String regex, String source, String replace_by, String should_contain) {
		Pattern pattern = Pattern.compile(regex);
		Matcher matcher = pattern.matcher(source);
		while (matcher.find()) {
			String match = matcher.group();
			if (match.contains(should_contain)) {
				Pattern replace_pattern = Pattern.compile(escape_metacharacters(match));
				Matcher replace_matcher = replace_pattern.matcher(source);
				source = replace_matcher.replaceAll(escape_metacharacters(replace_by));
			}
		}
		return source;
	}

	// *****************************************************************************

	// *****************************************************************************
	// String normalization methods.

	// Removes spaces at the beginning and at the end of s and duplicate spaces
	// within s.
	public static String cleanup_spaces(String s) {
		// In regex, anchors are not used to match characters. Instead, they match a
		// position i.e. before, after, or between characters.
		// To match start and end of line, we use the following anchors:
		// - Caret (^) matches the position before the first character in the string.
		// - Dollar ($) matches the position after the last character in the string.
		// Note that while we have to escape characters in the regex by "\\" (one '\'
		// for Java and one for the regex), it suffices to escape characters in a Java
		// string by a single "\".
		s = s.replaceAll("^\\s*", "").replaceAll("\\s*$", "").replaceAll("\\s+", " ");
		return s;
	}

	// Removes line breaks within s and cleans up duplicate spaces (that are
	// possibly created by this modification).
	public static String remove_line_breaks(String s) {
		return cleanup_spaces(s.replaceAll("\\n", ""));
	}

	// Returns the number of opening braces '(' in s.
	public static int count_opening_braces(String s) {
		return StringUtils.countMatches(s, "(");
	}

	// Returns the number of closing braces ')' in s.
	public static int count_closing_braces(String s) {
		return StringUtils.countMatches(s, ")");
	}

	// Returns true if there are as many opening braces as closing braces in s.
	public static boolean has_balanced_braces(String s) {
		return count_opening_braces(s) == count_closing_braces(s);
	}

	// Removes unmatched braces at the beginning and at the end of s.
	// This only works in very trivial cases like "(x+3))" but it suffices for our
	// purpose where s is a regex match that is most probably nearly balanced.
	public static String cleanup_braces(String s) {
		s = cleanup_spaces(s);
		int opening_braces = count_opening_braces(s);
		int closing_braces = count_closing_braces(s);
		while (opening_braces > closing_braces && s.substring(0, 1).equals("(")) {
			s = s.substring(1);
			opening_braces--;
		}
		while (opening_braces < closing_braces && s.substring(s.length() - 1, s.length()).equals(")")) {
			s = s.substring(0, s.length() - 1);
			closing_braces--;
		}
		while (s.length() > 4 && s.substring(0, 2).equals("((")
				&& s.substring(s.length() - 2, s.length()).equals("))")) {
			s = s.substring(1, s.length() - 1);
		}
		return s;
	}

	// *****************************************************************************

	// *****************************************************************************
	// String comparison methods.

	// Returns the minimum number of operations to convert a to b (considering
	// insertions, deletions and substitutions of a single character).
	// Uses the classic dynamic programming approach.
	public static int get_edit_distance(String a, String b) {
		int m = a.length();
		int n = b.length();
		int dp[][] = new int[m + 1][n + 1];
		for (int i = 0; i <= m; i++) {
			for (int j = 0; j <= n; j++) {
				if (i == 0) {
					// If a is empty, the only option is to insert all characters of b.
					dp[i][j] = j;
				} else if (j == 0) {
					// If b is empty, the only option is to remove all characters of a.
					dp[i][j] = i;
				} else if (a.charAt(i - 1) == b.charAt(j - 1)) {
					// If the current characters are the same, we can just keep them.
					dp[i][j] = dp[i - 1][j - 1];
				} else {
					// Otherwise, we take the minimum of insert, remove or replace + 1.
					dp[i][j] = Math.min(Math.min(dp[i][j - 1], dp[i - 1][j]), dp[i - 1][j - 1]) + 1;
				}
			}
		}
		return dp[m][n];
	}

	// Returns the element of candidates that has minimum edit distance to s.
	public static String get_min_dist_string(String s, Set<String> candidates) {
		int min_dist = Integer.MAX_VALUE;
		String min_candidate = "";
		for (String candidate : candidates) {
			int dist = get_edit_distance(s, candidate);
			if (dist < min_dist) {
				min_dist = dist;
				min_candidate = candidate;
			}
		}
		return min_candidate;
	}

	// *****************************************************************************

	// *****************************************************************************
	// SMT-related methods and fields.

	// Removes names from source, since these are not needed for this project.
	// Example: "(assert (! (= (f 0) 1) :named A0))" becomes "(assert (= (f 0) 1))".
	// Possibly throws a Proof_Exception if source is not well-formed according to
	// the SMT-LIBv2 language specification.
	public static String remove_names(String source) throws Proof_Exception {
		if (source.contains(":named")) {
			String regex = "\\(! .*? :named .*?\\)";
			String match = match_first(regex, source);
			String match_regex = "\\(! .*? :named";
			match = match_first(match_regex, match);
			String content = match.substring(3, match.length() - 7);
			source = replace_first(regex, source, content);
		}
		return source;
	}

	private static Let_Wrapper find_let_expression(String source) throws Proof_Exception {
		if (!source.contains("(let ((")) {
			return null;
		}

		List<String> variables = new ArrayList<String>();
		List<String> values = new ArrayList<String>();

		source = remove_line_breaks(source);
		int let_index = source.indexOf("(let (");
		String partial_source = source.substring(let_index + "(let (".length());

		String let_expression = "(let (";
		do {
			if (Thread.currentThread().isInterrupted()) {
				throw new Proof_Exception("Interrupted while removing let expressions");
			}

			int first_index = partial_source.indexOf("(");
			int last_index = partial_source.length() - 1;
			int open_brackets = 0;
			int close_brackets = 0;

			for (int i = first_index; i < partial_source.length(); i++) {
				if (partial_source.charAt(i) == '(') {
					open_brackets++;
				} else if (partial_source.charAt(i) == ')') {
					close_brackets++;
				}
				if (open_brackets > 0 && open_brackets == close_brackets) {
					last_index = i;
					break;
				}
			}

			String current_let_expression = partial_source.substring(0, last_index + 1);
			String let_match;
			if (variables.size() == 0) { // first temp variable
				let_match = current_let_expression.substring("(".length());
			} else {
				let_match = current_let_expression.substring(" (".length());
			}
			let_expression += current_let_expression;
			int first_index_of_space = let_match.indexOf(" ");
			String variable = let_match.substring(0, first_index_of_space);
			assert (variable.contains("a!"));
			String value = let_match.substring(first_index_of_space + 1, let_match.length() - 1); // remove the ")" at
																									// the end
			assert (has_balanced_braces(value));
			variables.add(variable);
			values.add(value);

			partial_source = partial_source.substring(last_index + 1);
		} while (partial_source.startsWith(" (a!"));

		let_expression += ')';
		return new Let_Wrapper(let_expression, source.indexOf(let_expression), variables, values);
	}

	public static String remove_let_expressions(String source) throws Proof_Exception {
		List<Let_Wrapper> let_expressions = new ArrayList<Let_Wrapper>();

		source = remove_line_breaks(source);
		String result = source;
		while (result.contains("(let ((")) {
			Let_Wrapper let = find_let_expression(result);
			let_expressions.add(let);
			result = result.substring(let.start_index + let.expr.length());
		}

		String source_without_let = source;
		for (Let_Wrapper let : let_expressions) {
			source_without_let = source_without_let.replace(let.expr, "");
			for (int i = 0; i < let.variables.size(); i++) {
				source_without_let = substitute(source_without_let, let.variables.get(i), let.values.get(i));
			}
			source_without_let = source_without_let.substring(0, source_without_let.length() - 1); // remove the last
																									// ")"
			assert (has_balanced_braces(source_without_let));
		}
		return source_without_let;
	}

	public static String remove_let_and_substitute(String source, String replaced, String replacement)
			throws Proof_Exception {
		source = remove_let_expressions(source);
		replaced = remove_let_expressions(replaced);
		replacement = remove_let_expressions(replacement);
		return substitute(source, replaced, replacement);
	}

	public static String substitute(String source, String replaced, String replacement) throws Proof_Exception {
		if (source.equals(replaced)) {
			return replacement;
		}
		source = remove_line_breaks(source);
		replaced = remove_line_breaks(replaced);
		replacement = remove_line_breaks(replacement);
		Pattern pattern = Pattern.compile("(?<=^|\\W)" + Pattern.quote(replaced));
		Matcher matcher = pattern.matcher(source);
		String result = matcher.replaceAll(Matcher.quoteReplacement(replacement));
		return result;

	}

	public static String get_name(String assertion) {
		try {
			if (assertion.contains(":named")) {
				String regex = "\\(! .*? :named .*?\\)";
				String match = match_first(regex, assertion);
				String match_regex = ":named .*?\\)";
				match = cleanup_spaces(match_first(match_regex, match));
				String name = match.substring(7, match.length() - 1);
				return name;
			}
		} catch (Proof_Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	// Removes comments (everything following after and including ';') from source,
	// since these are not needed for this project.$
	// Possibly throws a Proof_Exception if source is not well-formed according to
	// the SMT-LIBv2 language specification.
	public static String remove_comments(String source) throws Proof_Exception {
		if (source.contains(";")) {
			String regex = (";.*");
			String match = match_first(regex, source);
			source = replace_first(escape_metacharacters(match), source, "");
		}
		return source;
	}

	// Transforms the assertion in source to "(! <source> :named <name>)".
	// Throws a Proof_Exception if there is no assertion in source.
	public static String name_assertion(String source, String name) throws Proof_Exception {
		String regex = ("assert \\(.*\\)");
		String match = match_first(regex, source);
		String named_assertion = "assert (! " + match.substring(7, match.length() - 1) + " :named " + name + "))";
		source = replace_first(regex, source, named_assertion);
		return source;
	}

	// Rewrites the function-declaration with no arguments in source to a
	// constant-declaration with the same name.
	// Example: "(declare-fun a () Int)" becomes "(declare-const a Int)".
	public static String func_decl_to_const_decl(String source) {
		try {
			String regex = "declare-fun [^\\s]+ \\(\\)";
			String match = match_first(regex, source);
			source = "(declare-const " + match.substring(12, match.length() - 3) + source.substring(match.length() + 1);
		} catch (Proof_Exception e) {
			// Do nothing, just return the source.
		}
		return source;
	}

	// Rewrites source such that it can be parsed by Vampire. Returns an array of
	// strings as the rewriting might split up source into multiple expressions.
	public static String[] vampirize(String source) throws Proof_Exception {
		// Vampire distinguishes between "|Token|" and "Token" while Z3 does not.
		source = remove_vertical_bars(source);
		// Vampire does not have built-in "/" for division but understands "div".
		source = rewrite_divison_symbol(source);
		// Vampire does not support the prefix index notation "(_ a b)".
		// We need to rewrite this as "a_b".
		source = rewrite_index_notation(source);
		// Vampire does not support the unary minus "-x".
		// We need to rewrite this as "(- 0 x)".
		source = rewrite_unary_minus_symbol(source);
		// Vampire requires sort declarations to be given with another argument, i.e. in
		// the form "(declare-sort <name> 0)" and not just "(<declare-sort name>)".
		source = rewrite_sort_declaration(source);
		// Vampire does not support the identifier "implies".
		// We need to rewrite it to "=>".
		source = source.replace("implies", "=>");
		// Vampire does not support the overloaded "bv2int" symbol.
		// Therefore, we infer and declare the required (bit-width specific) sorts and
		// declare the corresponding "bv2int_n" functions where "n" is the bit width
		// that comes from explicit type name in the variable declaration context.
		String[] sources = rewrite_bitvec_symbol(source);
		return sources;
	}

	// Removes all vertical bars ("|") around words in source.
	// That is, "|Token|" becomes "Token".
	public static String remove_vertical_bars(String source) {
		if (source.contains("|")) {
			String regex = "\\|[^\\|\\s]*\\|";
			List<String> matches = match_all(regex, source);
			for (String match : matches) {
				String token_name = match.substring(1, match.length() - 1);
				source = replace_all(escape_metacharacters(match), source, token_name);
			}
		}
		return source;
	}

	// Rewrites "/" to "div" in source.
	// That is, "(/ a b)" becomes "(div a b)".
	public static String rewrite_divison_symbol(String source) {
		if (source.contains("/")) {
			source = source.replaceAll("\\(\\/ ", "(div ");
		}
		return source;
	}

	// Rewrites prefix index notation to infix index notation in source.
	// That is, "(_ a b)" becomes "a_b".
	public static String rewrite_index_notation(String source) throws Proof_Exception {
		String regex = "\\(_ (\\S*?) (\\S*?)\\)";
		while (source.contains("_")) {
			String a = match_first("\\(_ (\\S*?) ", source);
			a = a.substring(3, a.length() - 1);
			String b = match_first(" (\\S*?)\\)", source.substring(a.length() + 2));
			b = b.substring(1, b.length() - 1);
			source = replace_first(regex, source, ("(" + a + "_" + b + ")"));
		}
		return source;
	}

	// Rewrites unary minuses to binary ones in source.
	// That is, "-x" becomes "(- 0 x)".
	public static String rewrite_unary_minus_symbol(String source) {
		if (source.contains("-")) {
			// Note that only looking for "-" is kind of problematic as it might just be a
			// hyphen between two words so instead we look for both " -x " and "(-x)".
			// We still have to be careful not to modify a binary minus by accident.
			String spaces_regex = "\\s-(\\S*?)\\s";
			List<String> matches = match_all(spaces_regex, source);
			for (String match : matches) {
				String token_name = match.substring(2, match.length() - 1);
				source = replace_first(spaces_regex, source, " (- 0 " + token_name + ") ");
			}
			String braces_regex = "\\(-(\\S*?)\\)";
			matches = match_all(braces_regex, source);
			for (String match : matches) {
				String token_name = match.substring(2, match.length() - 1);
				source = replace_first(braces_regex, source, "(- 0 " + token_name + ")");
			}
			String mixed_regex = " -(\\S*?)\\)";
			matches = match_all(mixed_regex, source);
			for (String match : matches) {
				String token_name = match.substring(2, match.length() - 1);
				source = replace_first(mixed_regex, source, "(- 0 " + token_name + "))");
			}
		}
		return source;
	}

	// Handles bit-vectors in source so that they can be processed by Vampire.
	// "bv2int" is an interpreted function from the bit-vectors theory (in the
	// SMT-LIB standard it is called "bv2nat", but Z3 calls it "bv2int"). This is an
	// overloaded function, meaning we can call it with bit-vectors of arbitrary
	// lengths, that is, variables of types "BV_32", "BV_16", "BV_8", and so on.
	// Z3 will then look at the type of the variable and will internally call the
	// corresponding function "bv2int_32", "bv2int_16", ...
	// Vampire cannot do this automatically (it does not support bit-vectors), so
	// for every call of the form "bv2int x", we need to look at the declared
	// type of "x", which will be "BV_n". We then need to define "BV_n" as an
	// uninterpreted sort, declare "bv2int_n" as an uninterpreted function from
	// "BV_n" to "Int" and replace "bv2int x" by "bv2int_n x".
	// Example: "(forall ((x BV_32)) (P (bv2int x)))"
	// inferred requirements:
	// 1. "(declare-sort BV_32)"
	// 2. "(declare-fun bv2int_32 (BV_32) Int)"
	// Warning!!! This method will fail if:
	// a) The argument of "bv2int" is non-atomic.
	// b) The argument of "bv2int" is free in "smt_command" (e.g. it's a constant).
	// c) There is shadowing of variable names within "smt_command".
	// See:
	// https://gitlab.inf.ethz.ch/bugariua/axioms/-/blob/master/src/minimizer/minimizer.py
	// (method def __vampire_commands(self)).
	// Returns an array of strings as the rewriting might split up source into
	// multiple expressions.
	public static String[] rewrite_bitvec_symbol(String source) {
		try {
			if (source.contains("bv2int")) {
				// We assume source to have the form: "(forall ((x BV_32)) (P (bv2int x)))".
				String bitvec_regex = "\\(bv2int (.*?)\\)";
				String bitvec = match_first(bitvec_regex, source);
				// bitvec: "(bv2int x)".
				String argument = bitvec.substring(8, bitvec.length() - 1);
				// argument: "x";
				String argument_declaration_regex = "\\(" + argument + " [^\\)]*?\\)";
				String argument_declaration = match_first(argument_declaration_regex, source);
				// argument_declaration: "(x BV_32)".
				String bitvec_type = argument_declaration.substring(2 + argument.length(),
						argument_declaration.length() - 1);
				// bitvec_type: "BV_32".
				String n = bitvec_type.substring(3);
				// n: "32".
				String bitvec_function = "bv2int_" + n;
				// bitvec_function: "bv2int_32".
				String sort_decl = "(declare-sort " + bitvec_type + ")";
				// sort_decl: "(declare-sort BV_32)".
				String func_decl = "(declare-fun " + bitvec_function + " (" + bitvec_type + ") Int)";
				// func_decl: "(declare-fun bv2int_32 (BV_32) Int)".
				return new String[] { sort_decl, func_decl, source.replace("bv2int", bitvec_function) };
				// Modified source: "(forall ((x BV_32)) (P (bv2int_32 x)))".
			} else {
				return new String[] { source };
			}
		} catch (Exception e) {
			// Since above procedure may very well fail, we just return the unmodified
			// source if that happens.
			return new String[] { source };
		}
	}

	// Rewrites "(<declare-sort name>)" in source to "(declare-sort <name> 0)".
	public static String rewrite_sort_declaration(String source) {
		if (source.contains("(declare-sort")) {
			String regex = "\\(declare-sort \\S*\\)";
			List<String> matches = match_all(regex, source);
			for (String match : matches) {
				String sort_name = match.substring(14, match.length() - 1);
				source = "(declare-sort " + sort_name + " 0)";
			}
		}
		return source;
	}

	// Rewrites source such that both user-defined names and built-in types
	// correspond to the ones collected in the input by the names set.
	public static String devampirize(String source, Set<String> names) {
		// Vampire adds 'apostrophes' to some user-defined names in its proof. If we
		// e.g. declare an uninterpreted function called P, Vampire will change every
		// occurrence of P in the proof to 'P'. In order to compare the names of
		// functions in the proof with the names of functions in the input, we need to
		// remove these 'apostrophes'.
		if (source.contains("'")) {
			String regex = "\\'[^']*?\\'";
			List<String> matches = match_all(regex, source);
			for (String match : matches) {
				String token_name = match.substring(1, match.length() - 1);
				if (names.contains(token_name)) {
					// We only rewrite the occurrence if it corresponds to some user-defined name.
					source = replace_all_if(regex, source, token_name, match);
				}
			}
		}
		// Vampire adds '$' in front of built-in types (e.g. $int). It treats Booleans
		// even stranger. Namely, it uses "$o" for them and it also prepends "$true" and
		// "$false" by dollar signs. We want to remove all these since regex is confused
		// by them and they do not seem to be beneficial.
		if (source.contains("$")) {
			source = source.replace("$int", "Int");
			source = source.replace("$o", "Bool");
			source = source.replace("$true", "true");
			source = source.replace("$false", "false");
		}
		return source;
	}

	// Rewrites source so that some common expressions used in Vampire proofs are
	// replaced by the corresponding SMT-LIBv2 symbols.
	public static String replace_vampire_ops_with_symbols(String source) {
		if (source.contains("$greater(")) {
			source = source.replace("$greater", ">");
		}
		if (source.contains("$less")) {
			source = source.replace("$less", "<");
		}
		if (source.contains("$greatereq(")) {
			source = source.replace("$greatereq", ">=");
		}
		if (source.contains("$lesseq(")) {
			source = source.replace("$lesseq", "<=");
		}
		if (source.contains("$sum(")) {
			source = source.replace("$sum", "+");
		}
		if (source.contains("$difference(")) {
			source = source.replace("$difference", "-");
		}
		if (source.contains("$uminus(")) {
			source = source.replace("$uminus", "-");
		}
		if (source.contains("~")) {
			source = source.replace("~", "not");
		}
		return source;
	}

	// *****************************************************************************

	// *****************************************************************************
	// Vampire_Proof_Analyser-related methods.

	// If source is formatted as a line from a Vampire proof, then this returns the
	// number of that line as a string. Otherwise returns an empty string.
	public static String get_line_number(String source) {
		// Example: "2. ! [X0 : int] : f(X0) = 6 [input]" has line_number "2".
		String line_number;
		try {
			line_number = match_first("(\\d+)\\.", source);
			// Crop away the dot.
			line_number = line_number.substring(0, line_number.length() - 1);
			return line_number;
		} catch (Proof_Exception e) {
		}
		return "";
	}

	// If source is formatted as a line from a Vampire proof that references some
	// other lines as premises, then this returns the line numbers of those
	// premises. Otherwise returns an empty list.
	public static List<String> get_line_reference_numbers(String source) {
		// Example "16. f(X0) = 6 [cnf transformation 2]" has line 2 as a premise, as it
		// references "[cnf transformation 2]".
		// Example: "2. ! [X0 : int] : f(X0) = 6 [input]" from above references only
		// "[input]" and therefore has no premises.
		String references;
		try {
			references = match_last("\\[[^\\]]*\\]", source);
			return match_all("\\d+", references);
		} catch (Proof_Exception e) {
			return new LinkedList<String>();
		}
	}

	// If source is formatted as a line from a Vampire proof that includes some
	// quantified variables, then this returns a list that contains for each of them
	// a pair of strings of the form (name, type). Otherwise returns an empty list.
	public static List<String[]> get_line_quantified_variables_and_types(String source) {
		List<String[]> line_quant_vars = new LinkedList<String[]>();
		String source_regex = "\\[((\\S*?) : (\\S*?),?)*\\]";
		String def_regex = "(\\[)?((\\S*?) : (\\S*?))(\\,|\\])";
		String name_regex = "(\\[)?(\\S*?) :";
		String type_regex = ": (\\S*?)(\\,|\\])";
		// Example occurrence in the proof: "[X1 : int,X0 : T@U()]".
		// source_regex matches "[X1 : int,X0 : T@U()]".
		// def_regex matches both "[X1 : int," and "X0 : T@U()]".
		// name_regex matches both "[X1" and "X0".
		// type_regex matches both ": int," and ": T@U()]".
		for (String match_source : match_all(source_regex, source)) {
			for (String match : match_all(def_regex, match_source)) {
				try {
					// Find variable.
					String name = match_first(name_regex, match);
					// Cleanup.
					if (name.contains("[")) {
						name = name.substring(1, name.length() - 2);
					} else {
						name = name.substring(0, name.length() - 2);
					}
					// Find type.
					String type = match_first(type_regex, match);
					// Cleanup.
					type = type.substring(2, type.length() - 1);
					line_quant_vars.add(new String[] { name, type });
				} catch (Proof_Exception e) {
				}
			}
		}
		return line_quant_vars;
	}

	// Returns a list of function applications of f_name in source.
	// Returns an empty list if there are none.
	public static List<String> extract_function_applications(String source, String f_name) {
		List<String> out = new LinkedList<String>();
		f_name = escape_metacharacters(f_name);
		for (String match : match_all(f_name + "\\(.*?\\)", source)) {
			if (!has_balanced_braces(match)) {
				// It can happen that we do not match "far enough", e.g., if we source contains
				// "f(g(x))" and we look for "f", it can happen that the match gives us only
				// "f(g(x)", which is incomplete. On the other hand, it also can happen that we
				// matched "too far". In both cases we have to fix our match by considering a
				// bigger/smaller substring of the source.
				try {
					match = match_next_rbraces(match, source);
					match = unmatch_last_rbraces(match);
				} catch (Proof_Exception e) {
					// If this fails, we just ignore the function application.
					continue;
				}
			}
			// Handle nested applications of the same function.
			if (match.substring(f_name.length()).contains(f_name)) {
				out.addAll(extract_function_applications(match.substring(f_name.length()), f_name));
			}
			out.add(match);
		}
		return out;
	}

	// Returns a list of concrete values from inequalities in source where one side
	// is the variable
	// Example: If source contains "7 != X0" and variable is "X0", then the returned
	// list contains "7".
	// Example: If source contains "(false != X1)" and variable is "X1", then the
	// returned list contains "false".
	// Returns an empty list if there are none.
	public static List<String> extract_inequalities(String variable, String source) {
		// We distinguish between two cases, depending on which side of the
		// inequality the variable is on. Furthermore, we assume that the inequality is
		// either surrounded by spaces or by braces.
		variable = escape_metacharacters(variable);
		List<String> out = new LinkedList<String>();
		String left_inequality_regex_spaces = " " + variable + " \\!\\= \\S* ";
		String left_inequality_regex_braces = "\\(" + variable + " \\!\\= \\S*\\)";
		String left_inequality_regex = "(" + left_inequality_regex_spaces + "|" + left_inequality_regex_braces + ")";
		for (String match : match_all(left_inequality_regex, source)) {
			String concrete_value = match.substring(variable.length() + 5, match.length() - 1);
			out.add(concrete_value);
		}
		String right_inequality_regex_spaces = " \\S* \\!\\= " + variable + " ";
		String right_inequality_regex_braces = "\\(\\S* \\!\\= " + variable + "\\)";
		String right_inequality_regex = "(" + right_inequality_regex_spaces + "|" + right_inequality_regex_braces + ")";
		for (String match : match_all(right_inequality_regex, source)) {
			String concrete_value = match.substring(1, match.length() - 5 - variable.length());
			out.add(concrete_value);
		}
		return out;
	}

	// Returns a list of terms including variable_2 that are compared to variable_1.
	// Example: If source contains "(X0 = X1 + 1)" and variable is "X0", then the
	// returned list contains "X1 + 1".
	public static List<String> extract_comparisons(String variable_1, String variable_2, String source) {
		// We assume that the comparison is surrounded by spaces.
		variable_1 = escape_metacharacters(variable_1);
		List<String> out = new LinkedList<String>();
		String comparison_regex = "\\(" + variable_1 + " \\= .*\\)";
		for (String match : match_all(comparison_regex, source)) {
			String compared_value = match.substring(variable_1.length() + 4, match.length() - 1);
			if (compared_value.contains(variable_2)) {
				out.add(compared_value);
			}
		}
		return out;
	}

	// If the given match, which is part of source, has MORE opening/left braces
	// (i.e. '(') than closing/right braces (i.e. ')'), then we INCREASE our match
	// up to (including) the next occurrence of a closing/right brace (i.e. ')')
	// until the number of left and right braces is the same.
	// Otherwise this just returns the unmodified match.
	public static String match_next_rbraces(String match, String source) throws Proof_Exception {
		// Count braces.
		int l_braces_count = match_all("\\(", match).size();
		int r_braces_count = match_all("\\)", match).size();
		while (l_braces_count > r_braces_count) {
			// Escape braces in the match so regex does not get confused.
			match = escape_metacharacters(match);
			// Create a regex that matches up to (including) the next occurrence of a
			// closing/right brace (i.e. ')').
			String temp_regex = match + "([^\\)]*)\\)";
			match = match_first(temp_regex, source);
			l_braces_count = match_all("\\(", match).size();
			r_braces_count = match_all("\\)", match).size();
		}
		return match;
	}

	// If the given match, which is part of source, has LESS opening/left braces
	// (i.e. '(') than closing/right braces (i.e. ')'), then we REDUCE our match
	// down to (including) the previous occurrence of a closing/right brace
	/// (i.e. ')') until the number of left and right braces is the same.
	// Otherwise this just returns the unmodified match.
	public static String unmatch_last_rbraces(String match) throws Proof_Exception {
		// Count braces.
		while (!has_balanced_braces(match)) {
			// Create a regex that matches a string until the first occurrence of a
			// closing/right brace (i.e. ')').
			String temp_regex = "[^\\)]*\\)";
			String curr = "";
			String new_match = "";
			for (String temp_match : match_all(temp_regex, match)) {
				// Sum up all the matches but the last one.
				new_match += curr;
				curr = temp_match;
			}
			match = new_match;
		}
		return match;
	}

	// Removes the stuff that Vampire adds around the SMT expression given in
	// source, which is assumed to be of the form "<number>. <expression> [input]".
	public static String simplify_preprocessing_line(String source) {
		// Examples:
		// For "[PP] input: 2. $false [input]" we want to return "$false".
		// For "[PP] input: 1. ! [X0 : $int] : ($greater(X0,$difference(0,1)) =>
		// $greater(f(X0),7)) [input]" we want to return "($greater(X0,$difference(0,1))
		// => $greater(f(X0),7))"
		try {
			String simplified_line = match_first("\\. .*? \\[input\\]", source);
			// Crop away the surroundings.
			simplified_line = simplified_line.substring(2, simplified_line.length() - 8);
			if (simplified_line.contains("]")) {
				// If that's the case, the expression in our simplified_line is prepended by a
				// listing of quantified variables of the form "[<quant_var> : <type>, ...]",
				// which we want to remove too.
				simplified_line = match_first("\\] \\: .*", simplified_line);
				simplified_line = simplified_line.substring(4);
			}
			return simplified_line;
		} catch (Proof_Exception e) {
			e.printStackTrace();
		}
		return source;
	}
	// *****************************************************************************
}