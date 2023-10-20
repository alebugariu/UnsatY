package evaluation;

public class Statistics {
	
	public int unsat_core_success;
	public int proof_generation_success;
	public int example_construction_success;
	public int example_minimization;
	public int ematching_success;
	
	private int benchmarks;
	
	public Statistics(int benchmarks) {
		this.benchmarks = benchmarks;
	}
	
	public void print_summary() {
		System.out.println("Results summary");
		System.out.println("Total number of benchmarks: " + benchmarks);
		System.out.println("Successful unsat core generation: " + unsat_core_success);
		System.out.println("Successful proof generation: " + proof_generation_success);
		System.out.println("Successful example construction: " + example_construction_success);
		System.out.println("Example minimization performed: " + example_minimization);
		System.out.println("Successful triggering terms generation: " + ematching_success);
	}

}
