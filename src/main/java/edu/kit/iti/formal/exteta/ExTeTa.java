package edu.kit.iti.formal.exteta;

import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.exteta.io.Report;
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.smv.ast.SMVModule;
import org.apache.commons.cli.*;

import javax.xml.bind.JAXBException;
import java.io.IOException;

public class ExTeTa {
    public static boolean DEBUG = true;

    public static void main(String[] args) {
        try {
            CommandLine cli = parse(args);
            run(cli);
        } catch (ParseException e) {
            Report.fatal(e.getMessage());
        } catch (JAXBException e) {
            Report.fatal(e.getLinkedException().getMessage());
        } catch (IOException e) {
            Report.fatal("IOExcepton: %s", e.getMessage());
        }
    }

    public static void run(CommandLine cli)
            throws ParseException, JAXBException, IOException {
        // xml
        Report.XML_MODE = cli.hasOption("x");

        //
        Runtime.getRuntime().addShutdownHook(new Thread(Report::close));

        //
        String tableFilename = cli.getOptionValue("t");
        String codeFilename = cli.getOptionValue("c");


        if (tableFilename == null || codeFilename == null) {
            Report.fatal("No code or table file given.");
            System.exit(1);
        }

        //
        GeneralizedTestTable table = Facade.readTable(tableFilename);
        TopLevelElements code = Facade.readProgram(codeFilename);

        TableTransformer tt = new TableTransformer(table);
        SMVModule modTable = tt.transform();
        SMVModule modCode = SymbExFacade.evaluateProgram(code);
        SMVModule mainModule = Facade.glue(modTable, modCode);

        boolean b = Facade.runNuXMV(tableFilename,
                mainModule, modTable, modCode);
    }

    private static CommandLine parse(String[] args) throws ParseException {
        CommandLineParser clp = new DefaultParser();

        Options options = new Options();
        options.addOption("x", false, "enable XML mode");
        options.addOption("t", "table", true, "the xml file of the table");
        options.addOption("o", "output", true, "ouput");
        options.addOption("c", "code", true, "program files");

        return clp.parse(options, args, true);
    }

}
