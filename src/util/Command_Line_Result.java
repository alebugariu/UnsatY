package util;

public class Command_Line_Result {

	public String error;
	public String output;

	public Command_Line_Result(String error, String output) {
		this.error = error;
		this.output = output;
	}

	@Override
	public String toString() {
		return "Standard output: " + output + "Error message: " + error;
	}
}