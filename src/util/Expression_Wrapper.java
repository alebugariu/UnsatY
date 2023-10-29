package util;

import com.microsoft.z3.Expr;

public class Expression_Wrapper {

	public Expr<?> expr;
	public int index; 
	public int var_index;
	
	public Expression_Wrapper(Expr<?> expr, int index, int var_index) {
		this.expr = expr;
		this.index = index;
		this.var_index = var_index;
	}
}
