package util.wrapper;

import java.util.List;

public class Let_Wrapper {
	
	public String expr;
	public String scope;
	public int scope_start_index;
	public List<String> variables;
	public List<String> values;
	
	public Let_Wrapper(String expr, String scope, int start_index, List<String> variables, List<String> values) {
		this.expr = expr;
		this.scope = scope;
		this.scope_start_index = start_index;
		this.variables = variables;
		this.values = values;
	}
	
	@Override
	public String toString() {
		return expr;
	}
	

}
