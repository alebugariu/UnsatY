package util.wrapper;

import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;

public class Pattern_Wrapper {
	
	public String expr;
	public Symbol[] vars;
	public Sort range;
	
	public Pattern_Wrapper(String expr, Symbol[] vars, Sort range ) {
		this.expr = expr;
		this.vars = vars;
		this.range = range;
	}

}
