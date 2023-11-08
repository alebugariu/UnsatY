package util.wrapper;

import java.util.List;

public class Let_Wrapper {
	
	public String expr;
	public int start_index;
	public List<String> variables;
	public List<String> values;
	
	public Let_Wrapper(String expr, int start_index, List<String> variables, List<String> values) {
		this.expr = expr;
		this.start_index = start_index;
		this.variables = variables;
		this.values = values;
	}
	
	@Override
	public String toString() {
		return expr;
	}
	

}
