/*******************************************************************************
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *   
 * Copyright (c) 2021-2023 ETH Zurich.
 *******************************************************************************/
package util;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;

/*
 * This class can be used to parse an expression from an unsat-proof generated
 * by Vampire to an Expr<?> that can be used with the Z3 API.
 */

public class Vampire_to_Z3_Parser {

	private String add_regex = "^\\+\\([^\\s]*\\,[^\\s]*\\)$";
	private String sub_regex = "^\\-\\([^\\s]*\\,[^\\s]*\\)$";
	private String uminus_regex = "^\\-[^\\s]*$";

	private Context context;

	private Map<String, FuncDecl<?>> declarations;

	public Vampire_to_Z3_Parser(Context context, Set<FuncDecl<?>> f_decls) {
		// Note: It is crucial to always use the same context, as otherwise it does not
		// know what we are talking about.
		this.context = context;
		this.declarations = new HashMap<String, FuncDecl<?>>();
		for (FuncDecl<?> f_decl : f_decls) {
			declarations.put(f_decl.getName().toString(), f_decl);
		}
	}

	public Expr<?> parse_to_expr(String s) {
		s = String_Utility.replace_vampire_ops_with_symbols(s);
		try {
			// First, we want to preprocess s so our regex methods below do not fail.
			s = String_Utility.cleanup_braces(String_Utility.cleanup_spaces(s));
			if (s.length() == 0) {
				return null;
			} else if (String_Utility.match_all("[^\\d]", s).isEmpty() && isInt(s)) {
				return context.mkInt(Integer.parseInt(s));
			} else if (isBoolTrue(s)) {
				return context.mkBool(true);
			} else if (isBoolFalse(s)) {
				return context.mkBool(false);
			} else if (isAdd(s)) {
				String a = String_Utility.match_first("^\\+\\([^\\s]*\\,", s);
				a = a.substring(2, a.length() - 1);
				String b = String_Utility.match_first("\\,[^\\s]*\\)$", s);
				b = b.substring(1, b.length() - 1);
				ArithExpr<?> expr_a = (ArithExpr<?>) parse_to_expr(a);
				ArithExpr<?> expr_b = (ArithExpr<?>) parse_to_expr(b);
				if (expr_a != null && expr_b != null) {
					return context.mkAdd(expr_a, expr_b);
				}
			} else if (isSub(s)) {
				String a = String_Utility.match_first("^\\-\\([^\\s]*\\,", s);
				a = a.substring(2, a.length() - 1);
				String b = String_Utility.match_first("\\,[^\\s]*\\)$", s);
				b = b.substring(1, b.length() - 1);
				ArithExpr<?> expr_a = (ArithExpr<?>) parse_to_expr(a);
				ArithExpr<?> expr_b = (ArithExpr<?>) parse_to_expr(b);
				if (expr_a != null && expr_b != null) {
					return context.mkSub(expr_a, expr_b);
				}
			} else if (isUminus(s)) {
				ArithExpr<?> expr_a = (ArithExpr<?>) parse_to_expr(s.substring(1));
				if (expr_a != null) {
					return context.mkUnaryMinus(expr_a);
				}
			} else {
				for (String declaration : declarations.keySet()) {
					if (s.startsWith(declaration)) {
						if (declarations.get(declaration).getArity() > 0 && s.length() > declaration.length() + 2) {
							// We have an uninterpreted function.
							// Remove the name of the function and the brackets that surround all the
							// arguments.
							s = s.substring(declaration.length() + 1, s.length() - 1);
							List<String> arguments = new LinkedList<String>();
							int i = 0;
							int brace_count = 0;
							String accumulator = "";
							while (i < s.length()) {
								String next_char = s.substring(i, i + 1);
								if (next_char.equals("(")) {
									brace_count++;
								} else if (next_char.equals(")")) {
									brace_count--;
								} else if (next_char.equals(",") && brace_count == 0) {
									arguments.add(accumulator);
									accumulator = "";
									i++;
									continue;
								}
								accumulator += next_char;
								i++;
							}
							arguments.add(accumulator);
							Expr<?>[] parsed_arguments = new Expr<?>[arguments.size()];
							for (int j = 0; j < arguments.size(); j++) {
								parsed_arguments[j] = parse_to_expr(arguments.get(j));
								if (parsed_arguments[j] == null) {
									return null;
								}
							}
							return context.mkApp(declarations.get(declaration), parsed_arguments);
						} else {
							// We have a user-defined constant.
							return context.mkConst(declarations.get(declaration));
						}
					}
				}
			}
		} catch (Exception e) {
			// If we encounter some unsupported operation or failed to parse s for other
			// reasons, we just do nothing and return null.
		}
		return null;
	}

	private boolean isInt(String s) {
		return String_Utility.match_all("[^-1234567890]", s).isEmpty();
	}

	private boolean isBoolTrue(String s) {
		return s.equals("true");
	}

	private boolean isBoolFalse(String s) {
		return s.equals("false");
	}

	private boolean isAdd(String s) {
		for (String match : String_Utility.match_all(add_regex, s)) {
			if (s.startsWith(match)) {
				return true;
			}
		}
		return false;
	}

	private boolean isSub(String s) {
		for (String match : String_Utility.match_all(sub_regex, s)) {
			if (s.startsWith(match)) {
				return true;
			}
		}
		return false;
	}

	private boolean isUminus(String s) {
		for (String match : String_Utility.match_all(uminus_regex, s)) {
			if (s.startsWith(match)) {
				return true;
			}
		}
		return false;
	}

}
