package evaluation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class Statistics {

	public int unsat_core_success;
	public int proof_generation_success;
	public int example_construction_success;
	public int example_minimization;
	public int ematching_success;

	public List<Integer> formulas;
	public List<Integer> quantifiers;
	public List<Integer> unsat_core_formulas;
	public List<Integer> unsat_core_quantifiers;

	private int benchmarks;

	public Statistics(int benchmarks) {
		this.benchmarks = benchmarks;
		this.formulas = new ArrayList<Integer>();
		this.quantifiers = new ArrayList<Integer>();
		this.unsat_core_formulas = new ArrayList<Integer>();
		this.unsat_core_quantifiers = new ArrayList<Integer>();
	}

	public void print_summary() {
		System.out.println("Results summary");
		System.out.println("Total number of benchmarks: " + benchmarks);
		System.out.println(
				"Number of formulas (min-max): " + Collections.min(formulas) + "-" + Collections.max(formulas));
		System.out.println("Number of quantifiers (min-max): " + Collections.min(quantifiers) + "-"
				+ Collections.max(quantifiers));
		System.out.println("Successful unsat core generation: " + unsat_core_success);
		System.out.println("Number of unsat core formulas (min-max): " + Collections.min(unsat_core_formulas) + "-"
				+ Collections.max(unsat_core_formulas));
		System.out.println("Number of unsat core quantifiers (min-max): " + Collections.min(unsat_core_quantifiers)
				+ "-" + Collections.max(unsat_core_quantifiers));
		System.out.println("Successful proof generation: " + proof_generation_success);
		System.out.println("Successful example construction: " + example_construction_success);
		System.out.println("Example minimization performed: " + example_minimization);
		System.out.println("Successful triggering terms generation: " + ematching_success);
	}

}
