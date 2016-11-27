package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextLexer;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextParser;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.IOException;
import java.util.List;

/**
 * Created by weigl on 11.06.14.
 */

@Parameters(separators = "=",
        commandNames = "view",
        commandDescription = "Prints the ast from the given text input")
public class AstViewer extends App {
    @Parameter(description = "file to read", names = "--file")
    public String file;

    public void execute() throws IOException {

        StructuredTextLexer lexer = new StructuredTextLexer(new ANTLRFileStream(file));
        StructuredTextParser parser = new StructuredTextParser(new CommonTokenStream(lexer));

        List<TopLevelElement> topLevel = parser.start().ast;

        for (TopLevelElement topLevelElement : topLevel) {
            System.out.println(topLevelElement);
        }

    }
}
