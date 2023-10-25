package evaluation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

public class Statistics {

	public AtomicInteger unsat_core_success;
	public AtomicInteger proof_generation_success;
	public AtomicInteger example_construction_success;
	public AtomicInteger example_minimization;
	public AtomicInteger ematching_success;

	public List<Integer> formulas;
	public List<Integer> quantifiers;
	public List<Integer> unsat_core_formulas;
	public List<Integer> unsat_core_quantifiers;
	public List<Integer> time; // in milliseconds

	private int benchmarks;

	public Statistics(int benchmarks) {
		this.benchmarks = benchmarks;
		this.unsat_core_success = new AtomicInteger(0);
		this.proof_generation_success = new AtomicInteger(0);
		this.example_construction_success = new AtomicInteger(0);
		this.example_minimization = new AtomicInteger(0);
		this.ematching_success = new AtomicInteger(0);
		this.formulas = Collections.synchronizedList(new ArrayList<Integer>());
		this.quantifiers = Collections.synchronizedList(new ArrayList<Integer>());
		this.unsat_core_formulas = Collections.synchronizedList(new ArrayList<Integer>());
		this.unsat_core_quantifiers = Collections.synchronizedList(new ArrayList<Integer>());
		this.time = Collections.synchronizedList(new ArrayList<Integer>());
	}

	public void print_summary() {
		String summary = "Results summary" + "\n" + "Total number of benchmarks: " + benchmarks + "\n"
				+ "Number of formulas (min - max): " + (formulas.isEmpty() ? "N/A" : Collections.min(formulas)) + " - "
				+ (formulas.isEmpty() ? "N/A" : Collections.max(formulas)) + "\n" + "Number of quantifiers (min - max): "
				+ (quantifiers.isEmpty() ? "N/A" : Collections.min(quantifiers)) + " - "
				+ (quantifiers.isEmpty() ? "N/A" : Collections.max(quantifiers)) + "\n"
				+ "Successful unsat core generation: " + unsat_core_success + "\n"
				+ "Number of unsat core formulas (min - max): "
				+ (unsat_core_formulas.isEmpty() ? "N/A" : Collections.min(unsat_core_formulas)) + " - "
				+ (unsat_core_formulas.isEmpty() ? "N/A" : Collections.max(unsat_core_formulas)) + "\n"
				+ "Number of unsat core quantifiers (min - max): "
				+ (unsat_core_quantifiers.isEmpty() ? "N/A" : Collections.min(unsat_core_quantifiers)) + " - "
				+ (unsat_core_quantifiers.isEmpty() ? "N/A" : Collections.max(unsat_core_quantifiers)) + "\n"
				+ "Successful proof generation: " + proof_generation_success + "\n"
				+ "Successful example construction: " + example_construction_success + "\n"
				+ "Example minimization performed: " + example_minimization + "\n"
				+ "Successful triggering terms generation: " + ematching_success + "\n"
				+ "Processing time in milliseconds (min - max): " + (time.isEmpty() ? "N/A" : Collections.min(time))
				+ " - " + (time.isEmpty() ? "N/A" : Collections.max(time));
		System.out.println(summary);
	}

}
