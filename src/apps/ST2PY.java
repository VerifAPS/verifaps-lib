package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCModelBuilder;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextParser;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;

/**
 * Created by weigl on 09/09/14.
 */
@Parameters(commandDescription = "st2py", commandNames = "st2py")
public class ST2PY extends App {
    @Parameter(names = "files")
    public String[] files;

    public final void execute() throws IOException {
        for (String s : files) {
            String input = FileUtils.readFileToString(new File(s));

            StructuredTextParser parser = SFCModelBuilder.getStructuredTextParser(input);

            TopLevelElements top = new TopLevelElements(parser.start().ast);

            PythonPrinter pythonprinter = new PythonPrinter();
            top.visit(pythonprinter);
            System.out.println(pythonprinter.getOutput());
        }
    }
}

