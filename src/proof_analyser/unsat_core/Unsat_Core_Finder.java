package proof_analyser.unsat_core;

import java.io.File;

import com.microsoft.z3.BoolExpr;

import util.Proof_Exception;
import util.Verbal_Output;

public interface Unsat_Core_Finder {
	
	public boolean is_unsat(File smt_file, Verbal_Output verbal_output) throws Proof_Exception;
	
	public boolean is_unsat(BoolExpr[] formula, Verbal_Output verbal_output) throws Proof_Exception;

	public BoolExpr[] get_unsat_core();

}
