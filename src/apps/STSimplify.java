package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import edu.kit.iti.formal.automation.Console;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCFactory;
import edu.kit.iti.formal.automation.st0.ST0Factory;

import java.io.File;
import java.io.IOException;

/**
 * Created by weigl on 03/10/14.
 */
@Parameters(separators = "=", commandNames = "simplify", commandDescription = "ST to STO")
public class STSimplify extends App {

    @Parameter(names = "-i", required = true)
    private String input;


    @Parameter(names = "-o")
    private String output;

    public void execute() throws IOException {
        Console.info("ST to ST0 started");
        Console.info("Input file %s", input);
        Console.info("Output will written to %s", output);

        TopLevelElements ast = Transformer.parse(new File((input)));

        SFCFactory.injectPreamble(ast);
        TopLevelElements st0ast = ST0Factory.simplify(ast);
        Transformer.writeAST(new File(output), st0ast);
    }
}