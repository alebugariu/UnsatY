package proof_analyser.unsat_core;

import java.io.File;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

import util.Proof_Exception;
import util.Verbal_Output;

public abstract class Unsat_Core_Finder {
	
	protected Context context;
	
	public Unsat_Core_Finder(Context context) {
		this.context = context;
	}
	
	public abstract boolean is_unsat(File smt_file, Verbal_Output verbal_output) throws Proof_Exception;
	
	public abstract boolean is_unsat(BoolExpr[] formula, Verbal_Output verbal_output) throws Proof_Exception;

	public abstract BoolExpr[] get_unsat_core();

}
