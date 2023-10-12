package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

public class Command_Line_Utility {

	public static Command_Line_Result run_z3(File file) {
		try {
			String file_name = file.getCanonicalPath();
			String[] process_args = new String[] { "z3", "-T:" + String.valueOf(Setup.z3_timout), file_name };
			return run_process(process_args);
		}
		catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}

	public static Command_Line_Result run_process(String[] args) {
		try {
			Process process = new ProcessBuilder(args).start();

			BufferedReader stdError = new BufferedReader(new InputStreamReader(process.getErrorStream()));
			BufferedReader stdOutput = new BufferedReader(new InputStreamReader(process.getInputStream()));

			String error_message = "";
			String s;
			while ((s = stdError.readLine()) != null) {
				error_message += s + "\n";
			}

			String output = "";
			while ((s = stdOutput.readLine()) != null) {
				output += s + "\n";
			}
			return new Command_Line_Result(error_message, output);
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}

}
