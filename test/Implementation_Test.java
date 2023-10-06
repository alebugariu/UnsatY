/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.Test;

import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;

import util.Proof_Exception;
import util.String_Utility;
import util.Vampire_to_Z3_Parser;

/*
 * This class can be used to test whether the implementations of the static
 * methods that our proof analysis relies on behave as expected.
 */

public class Implementation_Test {

	// *****************************************************************************
	// Basic regex methods.

	public static String smt_func_decl_1 = "(declare-fun System.Collections.Generic.IEnumerable_1...System.Char () Int)";
	public static String smt_func_decl_1_const = "(declare-const System.Collections.Generic.IEnumerable_1...System.Char Int)";
	public static String smt_func_decl_1_escaped = "\\(declare\\-fun System\\.Collections\\.Generic\\.IEnumerable_1\\.\\.\\."
			+ "System\\.Char \\(\\) Int\\)";
	public static String smt_func_decl_2 = "(declare-fun false3961to3978_correct () Int)";
	public static String smt_func_decl_2_const = "(declare-const false3961to3978_correct Int)";
	public static String smt_func_decl_3 = "(declare-fun FStar.Pervasives_Tm_refine_47384bef739d1f0729fd782d351dc9a5\r\n"
			+ "             ()\r\n" + "             Term)";
	public static String smt_func_decl_3_const = "(declare-const FStar.Pervasives_Tm_refine_47384bef739d1f0729fd782d351dc9a5\r\n"
			+ "            \r\n" + "             Term)";

	public static String func_decl_regex = "\\(declare-fun \\S+ \\(\\) \\S+\\)";
	public static String const_decl_regex = "\\(declare-const \\S+ \\S+\\)";

	@Test
	public void test_escape_metacharacters() {
		System.out.print("Testing the method String_Utility.escape_metacharacters: \t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("\\(\\(\\$\\;\\.\\)\\)", String_Utility.escape_metacharacters("(($;.))"));
			assertEquals(smt_func_decl_1_escaped, String_Utility.escape_metacharacters(smt_func_decl_1));
			// Test what we actually want to use it for.
			assertEquals(smt_func_decl_1,
					String_Utility.match_first(String_Utility.escape_metacharacters(smt_func_decl_1), smt_func_decl_1));
			assertEquals(smt_func_decl_2,
					String_Utility.match_first(String_Utility.escape_metacharacters(smt_func_decl_2), smt_func_decl_2));
			assertEquals(smt_func_decl_3,
					String_Utility.match_first(String_Utility.escape_metacharacters(smt_func_decl_3), smt_func_decl_3));
			// Check that there are no side-effects.
			assertEquals(" foo", String_Utility.escape_metacharacters(" foo"));
			assertEquals("Lorem ipsum dolor sit amet",
					String_Utility.escape_metacharacters("Lorem ipsum dolor sit amet"));
			System.out.println("SUCCESS");
		} catch (AssertionError | Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_match_first() {
		System.out.print("Testing the method String_Utility.match_first: \t\t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("foo", String_Utility.match_first("foo", "  foobarbaz   "));
			assertEquals("foofoo", String_Utility.match_first("(foo)+", "foofoobar"));
			assertEquals(String_Utility.remove_line_breaks(smt_func_decl_1),
					String_Utility.match_first(func_decl_regex, smt_func_decl_1));
			assertEquals(smt_func_decl_2, String_Utility.match_first(func_decl_regex, smt_func_decl_2));
			assertEquals(String_Utility.remove_line_breaks(smt_func_decl_3),
					String_Utility.match_first(func_decl_regex, String_Utility.remove_line_breaks(smt_func_decl_3)));
			assertEquals(smt_func_decl_1_const, String_Utility.match_first(const_decl_regex, smt_func_decl_1_const));
			assertEquals(smt_func_decl_2_const, String_Utility.match_first(const_decl_regex, smt_func_decl_2_const));
			assertEquals(String_Utility.remove_line_breaks(smt_func_decl_3_const), String_Utility
					.match_first(const_decl_regex, String_Utility.remove_line_breaks(smt_func_decl_3_const)));
			System.out.println("SUCCESS");
		} catch (AssertionError | Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	public void test_match_last() {
		System.out.print("Testing the method String_Utility.match_last: \t\t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("foofoo", String_Utility.match_last("(foo)+", "foofoobar"));
			assertEquals("foo", String_Utility.match_last("(foo)+", "foofoobarfoo"));
			assertEquals(String_Utility.match_first("foo", "  foobarbaz   "),
					String_Utility.match_last("foo", "  foobarbaz   "));
			// Check that there are no side-effects (same tests as in test_match_first).
			assertEquals(String_Utility.remove_line_breaks(smt_func_decl_1),
					String_Utility.match_last(func_decl_regex, smt_func_decl_1));
			assertEquals(smt_func_decl_2, String_Utility.match_last(func_decl_regex, smt_func_decl_2));
			assertEquals(String_Utility.remove_line_breaks(smt_func_decl_3),
					String_Utility.match_last(func_decl_regex, String_Utility.remove_line_breaks(smt_func_decl_3)));
			assertEquals(smt_func_decl_1_const, String_Utility.match_last(const_decl_regex, smt_func_decl_1_const));
			assertEquals(smt_func_decl_2_const, String_Utility.match_last(const_decl_regex, smt_func_decl_2_const));
			assertEquals(String_Utility.remove_line_breaks(smt_func_decl_3_const), String_Utility
					.match_last(const_decl_regex, String_Utility.remove_line_breaks(smt_func_decl_3_const)));
			System.out.println("SUCCESS");
		} catch (AssertionError | Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_match_all() {
		System.out.print("Testing the method String_Utility.match_all: \t\t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			List<String> expected_matches = new LinkedList<String>();
			expected_matches.add("foo");
			assertEquals(expected_matches, String_Utility.match_all("foo", "  foobarbaz   "));
			expected_matches.add(0, "foofoo");
			assertEquals(expected_matches, String_Utility.match_all("(foo)+", "foofoobarfoo"));
			assertEquals(1, String_Utility.match_all(func_decl_regex, smt_func_decl_1).size());
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_replace_first() {
		System.out.print("Testing the method String_Utility.replace_first: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("barbarbaz", String_Utility.replace_first("foo", "foobarbaz", "bar"));
			assertEquals("barbarbazfoo", String_Utility.replace_first("foo", "foobarbazfoo", "bar"));
			assertEquals("----..---", String_Utility.replace_first("\\.", "-.--..---", "-"));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_replace_all() {
		System.out.print("Testing the method String_Utility.replace_all: \t\t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("barbarbaz", String_Utility.replace_all("foo", "foobarbaz", "bar"));
			assertEquals("barbarbazbar", String_Utility.replace_all("foo", "foobarbazfoo", "bar"));
			assertEquals("---------", String_Utility.replace_all("\\.", "-.--..---", "-"));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_replace_all_if() {
		System.out.print("Testing the method String_Utility.replace_all_if: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("barbarbazfoo", String_Utility.replace_all_if("(foo)+", "foofoobarbazfoo", "bar", "oof"));
			assertEquals("-.------", String_Utility.replace_all_if("\\.+", "-.--..---", "-", ".."));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	// *****************************************************************************

	// *****************************************************************************
	// String normalization methods.

	public static String smt_expr_1 = "(assert (! (forall ((x0 Int)) (! (> (f x0) (f (- x0 1))) :pattern ( (g x0)))) :named A0))";
	public static String smt_expr_2 = "s = \"(assert (! (forall ((s1py0 T@U)(ipy0 Int)(vpy0 T@U)(lenpy0 Int)) (! (or (not"
			+ " (= (type s1py0) (SeqType (type vpy0)))) (= (Seq@sharp@Length (Seq@sharp@Build s1py0 ipy0 vpy0 lenpy0))"
			+ " lenpy0)) :pattern ((Seq@sharp@Length (Seq@sharp@Build s1py0 ipy0 vpy0 lenpy0))) )) :named A1))\"";
	public static String smt_expr_3 = "(assert (! (forall ((?a_1py2 Int)) (! (= (select2 ?a_1py2 (ptr2gid (ptr (base g___argv)"
			+ " 0)) size) 8) :pattern ((select2 ?a_1py2 (ptr2gid (ptr (base g___argv) 0)) size)) )) :named A1_50))";

	@Test
	public void test_cleanup_spaces() {
		System.out.print("Testing the method String_Utility.cleanup_spaces: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("foo", String_Utility.cleanup_spaces(" foo"));
			assertEquals("foo", String_Utility.cleanup_spaces("  foo"));
			assertEquals("bar", String_Utility.cleanup_spaces("bar "));
			assertEquals("bar", String_Utility.cleanup_spaces("bar  "));
			assertEquals("baz", String_Utility.cleanup_spaces("     baz     "));
			assertEquals("Hello world!", String_Utility.cleanup_spaces("   Hello     world!    "));
			// Check that there are no side-effects.
			assertEquals(smt_func_decl_1, String_Utility.cleanup_spaces(smt_func_decl_1));
			assertEquals(smt_func_decl_1_const, String_Utility.cleanup_spaces(smt_func_decl_1_const));
			assertEquals(smt_func_decl_2, String_Utility.cleanup_spaces(smt_func_decl_2));
			assertEquals(smt_func_decl_2_const, String_Utility.cleanup_spaces(smt_func_decl_2_const));
			assertEquals(smt_expr_1, String_Utility.cleanup_spaces(smt_expr_1));
			assertEquals(smt_expr_2, String_Utility.cleanup_spaces(smt_expr_2));
			assertEquals(smt_expr_3, String_Utility.cleanup_spaces(smt_expr_3));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_remove_line_breaks() {
		System.out.print("Testing the method String_Utility.remove_line_breaks: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("foobarbaz", String_Utility.remove_line_breaks("foo\nbar\nbaz"));
			assertEquals("foo bar baz", String_Utility.remove_line_breaks("foo\n bar\n baz"));
			assertEquals("foo", String_Utility.remove_line_breaks("foo               \n"));
			// Check that there are no side-effects.
			assertEquals(smt_func_decl_1, String_Utility.remove_line_breaks(smt_func_decl_1));
			assertEquals(smt_func_decl_1_const, String_Utility.remove_line_breaks(smt_func_decl_1_const));
			assertEquals(smt_func_decl_2, String_Utility.remove_line_breaks(smt_func_decl_2));
			assertEquals(smt_func_decl_2_const, String_Utility.remove_line_breaks(smt_func_decl_2_const));
			assertEquals(smt_expr_1, String_Utility.remove_line_breaks(smt_expr_1));
			assertEquals(smt_expr_2, String_Utility.remove_line_breaks(smt_expr_2));
			assertEquals(smt_expr_3, String_Utility.remove_line_breaks(smt_expr_3));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}

	}

	@Test
	public void test_count_opening_braces() {
		System.out.print("Testing the method String_Utility.count_opening_braces: \t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals(0, String_Utility.count_opening_braces(""));
			assertEquals(0, String_Utility.count_opening_braces(" "));
			assertEquals(0, String_Utility.count_opening_braces("foo baz bar."));
			assertEquals(0, String_Utility.count_opening_braces(")))"));
			assertEquals(1, String_Utility.count_opening_braces("("));
			assertEquals(1, String_Utility.count_opening_braces("()"));
			assertEquals(3, String_Utility.count_opening_braces("((("));
			assertEquals(5, String_Utility.count_opening_braces("()()()()()"));
			assertEquals(5, String_Utility.count_opening_braces("((()))(())"));
			assertEquals(2, String_Utility.count_opening_braces(smt_func_decl_1));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_count_closing_braces() {
		System.out.print("Testing the method String_Utility.count_closing_braces: \t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals(0, String_Utility.count_closing_braces(""));
			assertEquals(0, String_Utility.count_closing_braces(" "));
			assertEquals(0, String_Utility.count_closing_braces("foo baz bar."));
			assertEquals(0, String_Utility.count_closing_braces("((("));
			assertEquals(1, String_Utility.count_closing_braces(")"));
			assertEquals(1, String_Utility.count_closing_braces("()"));
			assertEquals(3, String_Utility.count_closing_braces(")))"));
			assertEquals(5, String_Utility.count_closing_braces("()()()()()"));
			assertEquals(5, String_Utility.count_closing_braces("((()))(())"));
			assertEquals(2, String_Utility.count_opening_braces(smt_func_decl_1));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_has_balanced_braces() {
		System.out.print("Testing the method String_Utility.has_balanced_braces: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals(true, String_Utility.has_balanced_braces(""));
			assertEquals(true, String_Utility.has_balanced_braces(" "));
			assertEquals(true, String_Utility.has_balanced_braces("foo baz bar."));
			assertEquals(false, String_Utility.has_balanced_braces("((("));
			assertEquals(false, String_Utility.has_balanced_braces(")))"));
			assertEquals(true, String_Utility.has_balanced_braces("()"));
			assertEquals(true, String_Utility.has_balanced_braces("()()()()()"));
			assertEquals(true, String_Utility.has_balanced_braces("((()))(())"));
			assertEquals(true, String_Utility.has_balanced_braces(smt_func_decl_1));
			assertEquals(true, String_Utility.has_balanced_braces(smt_func_decl_1_const));
			assertEquals(true, String_Utility.has_balanced_braces(smt_func_decl_2));
			assertEquals(true, String_Utility.has_balanced_braces(smt_func_decl_2_const));
			assertEquals(true, String_Utility.has_balanced_braces(smt_expr_1));
			assertEquals(true, String_Utility.has_balanced_braces(smt_expr_2));
			assertEquals(true, String_Utility.has_balanced_braces(smt_expr_3));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_cleanup_braces() {
		System.out.print("Testing the method String_Utility.test_cleanup_braces: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("foo baz bar.", String_Utility.cleanup_braces("foo baz bar."));
			assertEquals("", String_Utility.cleanup_braces("((("));
			assertEquals("", String_Utility.cleanup_braces(")))"));
			assertEquals("()", String_Utility.cleanup_braces("()"));
			assertEquals("()()()()()", String_Utility.cleanup_braces("()()()()()"));
			assertEquals("( ( ( ) ) ) ( ( ) )", String_Utility.cleanup_braces("( ( ( ) ) ) ( ( ) )"));
			// Check that there are no side-effects.
			assertEquals(smt_func_decl_1, String_Utility.cleanup_braces(smt_func_decl_1));
			assertEquals(smt_func_decl_1_const, String_Utility.cleanup_braces(smt_func_decl_1_const));
			assertEquals(smt_func_decl_2, String_Utility.cleanup_braces(smt_func_decl_2));
			assertEquals(smt_func_decl_2_const, String_Utility.cleanup_braces(smt_func_decl_2_const));
			assertEquals(smt_expr_1, String_Utility.cleanup_braces(smt_expr_1));
			assertEquals(smt_expr_2, String_Utility.cleanup_braces(smt_expr_2));
			assertEquals(smt_expr_3, String_Utility.cleanup_braces(smt_expr_3));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	// *****************************************************************************

	// *****************************************************************************
	// String comparison methods.

	@Test
	public void test_get_edit_distance() {
		System.out.print("Testing the method String_Utility.get_edit_distance: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals(1, String_Utility.get_edit_distance("cat", "cut"));
			assertEquals(3, String_Utility.get_edit_distance("abc", "def"));
			assertEquals(3, String_Utility.get_edit_distance("abcdef", "def"));
			assertEquals(3, String_Utility.get_edit_distance("sunday", "saturday"));
			assertEquals(7, String_Utility.get_edit_distance(smt_func_decl_1, smt_func_decl_1_const));
			assertEquals(7, String_Utility.get_edit_distance(smt_func_decl_2, smt_func_decl_2_const));
			assertEquals(7, String_Utility.get_edit_distance(smt_func_decl_3, smt_func_decl_3_const));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_get_min_dist_string() {
		System.out.print("Testing the method String_Utility.get_min_dist_string: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			Set<String> candidates = new LinkedHashSet<String>();
			candidates.add("cut");
			candidates.add(smt_func_decl_1_const);
			candidates.add(smt_func_decl_2_const);
			candidates.add(smt_func_decl_3_const);
			candidates.add(smt_expr_1);
			candidates.add(smt_expr_2);
			candidates.add(smt_expr_3);
			assertEquals("cut", String_Utility.get_min_dist_string("cat", candidates));
			assertEquals(smt_func_decl_1_const, String_Utility.get_min_dist_string(smt_func_decl_1, candidates));
			assertEquals(smt_func_decl_2_const, String_Utility.get_min_dist_string(smt_func_decl_2, candidates));
			assertEquals(smt_func_decl_3_const, String_Utility.get_min_dist_string(smt_func_decl_3, candidates));
			assertEquals(smt_expr_1, String_Utility.get_min_dist_string(smt_expr_1, candidates));
			assertEquals(smt_expr_2, String_Utility.get_min_dist_string(smt_expr_2, candidates));
			assertEquals(smt_expr_3, String_Utility.get_min_dist_string(smt_expr_3, candidates));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	// *****************************************************************************

	// *****************************************************************************
	// Input-related methods.

	@Test
	public void test_remove_smt_details() {
		System.out.print("Testing the method String_Utility.remove_smt_details: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("", String_Utility.remove_comments("; I am an SMT comment."));
			assertEquals("", String_Utility.remove_comments("; lajskdf7978123..,1.3,12.3??^;;"));
			assertEquals(smt_func_decl_1,
					String_Utility.remove_comments(smt_func_decl_1 + "; I am an SMT comment."));
			assertEquals("(assert (= (f 0) 1))",
					String_Utility.remove_names("(assert (! (= (f 0) 1) :named A0))"));
			// Check that there are no side-effects.
			String set_info = "(set-info :source | This benchmark originally named \"SExpressionSimplifier.Atom.Write$System.IO.TextWriter$notnull.smt2\" This benchmark was translated by Michal Moskal. |).";
			assertEquals(set_info, String_Utility.remove_comments(String_Utility.remove_names(set_info)));
			System.out.println("SUCCESS");
		} catch (AssertionError | Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_name_assertion() {
		System.out.print("Testing the method String_Utility.name_assertion: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("(assert (! (= (f 0) 1) :named A0))",
					String_Utility.name_assertion("(assert (= (f 0) 1))", "A0"));
			assertEquals(smt_expr_1,
					String_Utility.name_assertion(String_Utility.remove_names(smt_expr_1), "A0"));
			assertEquals(smt_expr_2,
					String_Utility.name_assertion(String_Utility.remove_names(smt_expr_2), "A1"));
			assertEquals(smt_expr_3,
					String_Utility.name_assertion(String_Utility.remove_names(smt_expr_3), "A1_50"));
			System.out.println("SUCCESS");
		} catch (AssertionError | Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_func_decl_to_const_decl() {
		System.out.print("Testing the method String_Utility.func_decl_to_const_decl: \t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("(declare-const a Int)", String_Utility.func_decl_to_const_decl("(declare-fun a () Int)"));
			assertEquals(smt_func_decl_1_const, String_Utility.func_decl_to_const_decl(smt_func_decl_1));
			assertEquals(smt_func_decl_2_const, String_Utility.func_decl_to_const_decl(smt_func_decl_2));
			assertEquals(String_Utility.remove_line_breaks(smt_func_decl_3_const),
					String_Utility.func_decl_to_const_decl(String_Utility.remove_line_breaks(smt_func_decl_3)));
			System.out.println("SUCCESS");
		} catch (AssertionError e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_vampirize() {
		System.out.print("Testing the method String_Utility.vampirize: \t\t\t\t\t");
		try {
			// Tests the sub-routine remove_vertical_bars.
			assertEquals("Test", String_Utility.vampirize("|Test|")[0]);
			assertEquals("T@U", String_Utility.vampirize("|T@U|")[0]);
			assertEquals("(declare-sort T@U 0)", String_Utility.vampirize("(declare-sort |T@U| 0)")[0]);
			// Tests the sub-routine rewrite_divison_symbol.
			assertEquals("(div x y)", String_Utility.vampirize("(/ x y)")[0]);
			assertEquals("(div 1 2)", String_Utility.vampirize("(/ 1 2)")[0]);
			assertEquals("(div arg0@@18 arg2@@1)", String_Utility.vampirize("(/ arg0@@18 arg2@@1)")[0]);
			// Tests the sub-routine rewrite_index_notation.
			assertEquals("(a_b)", String_Utility.vampirize("(_ a b)")[0]);
			assertEquals("(1_2)", String_Utility.vampirize("(_ 1 2)")[0]);
			assertEquals("(arg0@@18_arg2@@1)", String_Utility.vampirize("(_ arg0@@18 arg2@@1)")[0]);
			// Tests the sub-routine rewrite_unary_minus_symbol.
			assertEquals("(- 0 x)", String_Utility.vampirize("(-x)")[0]);
			assertEquals("(- 0 1)", String_Utility.vampirize("(-1)")[0]);
			assertEquals(" (- 0 1) ", String_Utility.vampirize(" -1 ")[0]);
			assertEquals("(- 0 arg0@@18)", String_Utility.vampirize("(-arg0@@18)")[0]);
			assertEquals("(assert (! (forall ((x0 Int)) (! (> (f x0) (f (- 0 1))) :pattern ( (g x0)))) :named A0))",
					String_Utility.vampirize(
							"(assert (! (forall ((x0 Int)) (! (> (f x0) (f -1)) :pattern ( (g x0)))) :named A0))")[0]);
			// Tests the subroutine rewrite_bitvec_symbol.
			String bitvec = "(forall ((x BV_32)) (P (bv2int x)))";
			assertEquals(3, String_Utility.vampirize(bitvec).length);
			assertEquals("(declare-sort BV_32)", String_Utility.vampirize(bitvec)[0]);
			assertEquals("(declare-fun bv2int_32 (BV_32) Int)", String_Utility.vampirize(bitvec)[1]);
			assertEquals("(forall ((x BV_32)) (P (bv2int_32 x)))", String_Utility.vampirize(bitvec)[2]);
			System.out.println("SUCCESS");
		} catch (Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
	}

	@Test
	public void test_devampirize() {
		System.out.print("Testing the method String_Utility.devampirize: \t\t\t\t\t");
		// Check that it does what it is supposed to.
		Set<String> names = new LinkedHashSet<String>();
		names.add("Test");
		assertEquals("Test", String_Utility.devampirize("'Test'", names));
		names.add("P");
		assertEquals("~P(X0) [input]", String_Utility.devampirize("~'P'(X0) [input]", names));
		// Check that there are no side-effects.
		assertEquals("'Other'", String_Utility.devampirize("'Other'", names));
		System.out.println("SUCCESS");
	}

	// *****************************************************************************

	// *****************************************************************************
	// Vampire_Proof_Analyser-related methods.

	public static String vampire_line_1 = "1. ! [X0 : $int] : ($greatereq(X0,0) => f(X0) = X0) [input]";
	public static String vampire_line_2 = "21. f(0) = 0 [resolution 19,10]";
	public static String vampire_line_3 = "1. ! [X1 : $int,X0 : $int] : (($greater(X0,$difference(0,1)) & $greater(X1,2)) => $greater(f(X0,X1),7)) [input]";
	public static String vampire_line_4 = "184. $sum(X2,$sum($uminus(X2),X3)) = X3 [forward demodulation 164,31]";

	private void prepare_vampire_lines() {
		Set<String> names = new LinkedHashSet<String>();
		names.add("f");
		vampire_line_1 = String_Utility.devampirize(vampire_line_1, names);
		vampire_line_2 = String_Utility.devampirize(vampire_line_2, names);
		vampire_line_3 = String_Utility.devampirize(vampire_line_3, names);
		vampire_line_4 = String_Utility.devampirize(vampire_line_4, names);
	}

	@Test
	public void test_get_line_number() {
		prepare_vampire_lines();
		System.out.print("Testing the method String_Utility.get_line_number: \t\t\t\t");
		// Check that it does what it is supposed to.
		assertEquals("1", String_Utility.get_line_number(vampire_line_1));
		assertEquals("21", String_Utility.get_line_number(vampire_line_2));
		assertEquals("1", String_Utility.get_line_number(vampire_line_3));
		assertEquals("184", String_Utility.get_line_number(vampire_line_4));
		System.out.println("SUCCESS");
	}

	@Test
	public void test_get_line_reference_numbers() {
		prepare_vampire_lines();
		System.out.print("Testing the method String_Utility.get_line_reference_numbers: \t\t\t");
		// Check that it does what it is supposed to.
		assertEquals("19", String_Utility.get_line_reference_numbers(vampire_line_2).get(0));
		assertEquals("10", String_Utility.get_line_reference_numbers(vampire_line_2).get(1));
		assertEquals("164", String_Utility.get_line_reference_numbers(vampire_line_4).get(0));
		assertEquals("31", String_Utility.get_line_reference_numbers(vampire_line_4).get(1));
		// Check that there are no side-effects.
		assertEquals(0, String_Utility.get_line_reference_numbers(vampire_line_1).size());
		assertEquals(0, String_Utility.get_line_reference_numbers(vampire_line_3).size());
		System.out.println("SUCCESS");
	}

	@Test
	public void test_get_line_quantified_variables_and_types() {
		prepare_vampire_lines();
		System.out.print("Testing the method String_Utility.get_line_quantified_variables_and_types: \t");
		// Check that it does what it is supposed to.
		assertEquals("X0", String_Utility.get_line_quantified_variables_and_types(vampire_line_1).get(0)[0]);
		assertEquals("Int", String_Utility.get_line_quantified_variables_and_types(vampire_line_1).get(0)[1]);
		assertEquals("X1", String_Utility.get_line_quantified_variables_and_types(vampire_line_3).get(0)[0]);
		assertEquals("Int", String_Utility.get_line_quantified_variables_and_types(vampire_line_3).get(0)[1]);
		assertEquals("X0", String_Utility.get_line_quantified_variables_and_types(vampire_line_3).get(1)[0]);
		assertEquals("Int", String_Utility.get_line_quantified_variables_and_types(vampire_line_3).get(1)[1]);
		// Check that there are no side-effects.
		assertEquals(0, String_Utility.get_line_quantified_variables_and_types(vampire_line_2).size());
		assertEquals(0, String_Utility.get_line_quantified_variables_and_types(vampire_line_4).size());
		System.out.println("SUCCESS");
	}

	@Test
	public void test_extract_function_applications() {
		prepare_vampire_lines();
		System.out.print("Testing the method String_Utility.extract_function_applications: \t\t");
		// Check that it does what it is supposed to.
		assertEquals("f(X0)", String_Utility.extract_function_applications(vampire_line_1, "f").get(0));
		assertEquals("f(0)", String_Utility.extract_function_applications(vampire_line_2, "f").get(0));
		assertEquals("g(x)", String_Utility.extract_function_applications("f(g(x)) + h(x)", "g").get(0));
		assertEquals("f(g(x))", String_Utility.extract_function_applications("f(g(x)) + h(x)", "f").get(0));
		assertEquals("g(x + 3)", String_Utility.extract_function_applications("f(g(x + 3))", "g").get(0));
		assertEquals("f(g(x + 3))", String_Utility.extract_function_applications("f(g(x + 3))", "f").get(0));
		assertEquals("f(g(sum(x,3)))",
				String_Utility.extract_function_applications("f(g(sum(x,3))) and f(x5 - 2)", "f").get(0));
		assertEquals("f(x5 - 2)",
				String_Utility.extract_function_applications("f(g(sum(x,3))) and f(x5 - 2)", "f").get(1));
		assertEquals("h(x0, x1)", String_Utility.extract_function_applications("h(x0, x1)", "h").get(0));
		assertEquals("f(x)", String_Utility.extract_function_applications("f(f(x))", "f").get(0));
		assertEquals("?v2!11(42)", String_Utility.extract_function_applications("?v2!11(42)", "?v2!11").get(0));
		// Check that there are no side-effects.
		assertEquals(1, String_Utility.extract_function_applications(vampire_line_1, "f").size());
		assertEquals(1, String_Utility.extract_function_applications(vampire_line_2, "f").size());
		System.out.println("SUCCESS");
	}

	@Test
	public void test_extract_inequalities() {
		System.out.print("Testing the method String_Utility.extract_inequalities: \t\t\t");
		// Check that it does what it is supposed to.
		assertEquals("7", String_Utility.extract_inequalities("X0", " 7 != X0 ").get(0));
		assertEquals("7", String_Utility.extract_inequalities("X0", "(7 != X0)").get(0));
		assertEquals("7", String_Utility.extract_inequalities("X0", " X0 != 7 ").get(0));
		assertEquals("7", String_Utility.extract_inequalities("X0", "(X0 != 7)").get(0));
		assertEquals("false", String_Utility.extract_inequalities("X1", " false != X1 ").get(0));
		assertEquals("false", String_Utility.extract_inequalities("X1", "(false != X1)").get(0));
		assertEquals("false", String_Utility.extract_inequalities("X1", " X1 != false ").get(0));
		assertEquals("false", String_Utility.extract_inequalities("X1", "(X1 != false)").get(0));
		// Check that there are no side-effects.
		assertEquals(0, String_Utility.extract_inequalities("X0", "(X1 != false)").size());
		System.out.println("SUCCESS");
	}

	@Test
	public void test_extract_comparisons() {
		System.out.print("Testing the method String_Utility.extract_comparisons: \t\t\t\t");
		// Check that it does what it is supposed to.
		assertEquals("X1", String_Utility.extract_comparisons("X0", "X1", "(X0 = X1)").get(0));
		assertEquals("X1 + 1", String_Utility.extract_comparisons("X0", "X1", "(X0 = X1 + 1)").get(0));
		System.out.println("SUCCESS");
	}

	@Test
	public void test_match_next_rbraces() {
		System.out.print("Testing the method String_Utility.match_next_rbraces: \t\t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("f(g(x))", String_Utility.match_next_rbraces("f(g(x", "f(g(x))"));
			assertEquals("h(f(g(x)) x)", String_Utility.match_next_rbraces("h(f(g(x))", "h(f(g(x)) x)"));
			assertEquals("f(g(x))", String_Utility.match_next_rbraces("f(g(", "f(g(x)) x)"));
			System.out.println("SUCCESS");
		} catch (AssertionError | Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
		// Note that these methods are also implicitly checked by
		// test_match_function_arguments.
	}

	// Tests whether the method unmatch_last_rbraces in util.Regex modifies
	// matches as expected.
	@Test
	public void test_unmatch_last_rbraces() {
		System.out.print("Testing the method String_Utility.unmatch_last_rbraces: \t\t\t");
		try {
			// Check that it does what it is supposed to.
			assertEquals("f(x)", String_Utility.unmatch_last_rbraces("f(x), X0)"));
			assertEquals("f(g(x))", String_Utility.unmatch_last_rbraces("f(g(x))))"));
			System.out.println("SUCCESS");
		} catch (AssertionError | Proof_Exception e) {
			System.out.println("FAILED. Reason: " + e.getMessage());
		}
		// Note that these methods are also implicitly checked by
		// test_match_function_arguments.
	}

	@Test
	public void test_simplify_preprocessing_line() {
		System.out.print("Testing the method String_Utility.simplify_preprocessing_line: \t\t\t");
		// Check that it does what it is supposed to.
		assertEquals("$false", String_Utility.simplify_preprocessing_line("[PP] input: 2. $false [input]"));
		assertEquals("($greater(X0,$difference(0,1)) => $greater(f(X0),7))", String_Utility.simplify_preprocessing_line(
				"[PP] input: 1. ! [X0 : $int] : ($greater(X0,$difference(0,1)) => $greater(f(X0),7)) [input]"));
		System.out.println("SUCCESS");
	}

	// *****************************************************************************

	// *****************************************************************************
	// Parsing-related methods.

	@Test
	public void test_parse_to_expr() {
		System.out.print("Testing the method Basic_Expr_Parser.parse_to_expr: \t\t\t\t");
		// Check that it does what it is supposed to.
		Context context = new Context();
		Vampire_to_Z3_Parser parser = new Vampire_to_Z3_Parser(context, new LinkedHashSet<FuncDecl<?>>());
		assertEquals("true", parser.parse_to_expr("true").toString());
		assertEquals("false", parser.parse_to_expr("false").toString());
		assertEquals("1", parser.parse_to_expr("1").toString());
		assertEquals("(+ 1 2)", parser.parse_to_expr("+(1,2)").toString());
		assertEquals("(- 4 3)", parser.parse_to_expr("-(4,3)").toString());
		assertEquals("(- 2)", parser.parse_to_expr("-2").toString());
		System.out.println("SUCCESS");
	}

	// *****************************************************************************
}