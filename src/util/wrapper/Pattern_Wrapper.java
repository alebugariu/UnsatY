package util.wrapper;

import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;

public class Pattern_Wrapper {
	
	public String expr;
	public Symbol[] vars; // over-approximation of the quantified variables appearing in this pattern
	public Sort range; // return type of the outer uninterpreted function
	
	public Pattern_Wrapper(String expr, Symbol[] vars, Sort range ) {
		this.expr = expr;
		this.vars = vars;
		this.range = range;
	}

}
