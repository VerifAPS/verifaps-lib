package edu.kit.iti.formal.exteta;

import java.io.IOException;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import edu.kit.formal.exteta.schema.ExtendedTestTableType;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;

public class ExTeTa {
	public static void main(String[] args) throws ParseException, JAXBException, IOException {
		CommandLine cli = parse(args);

		//
		ExtendedTestTableType table = Facade.readTable(cli.getOptionValue("t"));
		//
		List<TopLevelElement> code = Facade.readProgram(cli.getOptionValue("c"));
		//

		
		
	}

	private static CommandLine parse(String[] args) throws ParseException {
		CommandLineParser clp = new DefaultParser();

		Options options = new Options();
		options.addOption("t", "table", true, "the xml file of the table");
		options.addOption("o", "output", true, "ouput");
		options.addOption("c", "code", true, "program files");

		return clp.parse(options, args, true);
	}

}
