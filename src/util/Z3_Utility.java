package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

public class Z3_Utility {

	public static String run_command(File file) {
		try {
			String file_name = file.getCanonicalPath();
			String command = "z3 -T:" + Setup.z3_timout + " " + file_name;
			Process z3Process = Runtime.getRuntime().exec(command);
			BufferedReader output = new BufferedReader(new InputStreamReader(z3Process.getInputStream()));
			String result = "";
			String line = output.readLine();
			while (line != null) {
				result += line + "\n";
				line = output.readLine();
			}
			return result;
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}

}
