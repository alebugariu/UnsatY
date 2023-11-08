package util.wrapper;

import com.microsoft.z3.Expr;

public class Expression_Wrapper {

	public Expr<?> expr;
	public int var_index;
	
	public Expression_Wrapper(Expr<?> expr, int var_index) {
		this.expr = expr;
		this.var_index = var_index;
	}
}
