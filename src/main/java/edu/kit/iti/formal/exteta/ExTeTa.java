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
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.smv.Printer;
import edu.kit.iti.formal.smv.ast.Module;

public class ExTeTa {
	public static boolean DEBUG = true;
	
	public static void main(String[] args) throws ParseException, JAXBException, IOException {
		CommandLine cli = parse(args);	

		//
		String tableFilename = cli.getOptionValue("t");
		String codeFilename = cli.getOptionValue("c");

		
		if(tableFilename == null || codeFilename == null) {
			System.exit(1);
		}
		
		//
		GeneralizedTestTable table = Facade.readTable(tableFilename);
		List<TopLevelElement> code = Facade.readProgram(codeFilename);
		
		//
		//TableTransformer tt = new TableTransformer(table);
		//Module m = tt.transform();
		
		//System.out.println(Printer.toString(m));
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
