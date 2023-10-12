package proof_analyser.unsat_core;

import java.io.File;

import com.microsoft.z3.BoolExpr;

import util.Proof_Exception;
import util.Verbal_Output;

public class Command_Line_Unsat_Core_Finder implements Unsat_Core_Finder {

	@Override
	public boolean is_unsat(File smt_file, Verbal_Output verbal_output) throws Proof_Exception {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean is_unsat(BoolExpr[] formula, Verbal_Output verbal_output) throws Proof_Exception {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public BoolExpr[] get_unsat_core() {
		// TODO Auto-generated method stub
		return null;
	}

}
