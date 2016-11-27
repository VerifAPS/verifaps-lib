package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.Parameters;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextLexer;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextParser;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCFactory;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCModelBuilder;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import edu.kit.iti.formal.automation.st.visitors.StructuredTextHtmlPrinter;
import edu.kit.iti.formal.automation.st.visitors.StructuredTextPrinter;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;
import java.util.List;

/**
 * Created by weigl on 23/06/14.
 */
@Parameters(commandNames = "sfc")
public class SfcApp extends App {
    public void execute() throws IOException {
        SFCModelBuilder builder = new SFCModelBuilder("Scenario0_Final.xml");
        List<TopLevelElement> blocks = builder.build();

        SFCFactory.injectPreamble(blocks);


        STSimplifier stSimplifier = new STSimplifier(blocks);
        stSimplifier.transform();
        blocks = stSimplifier.getProcessed();

        StructuredTextPrinter s = new StructuredTextPrinter();
        s.setPrintComments(false);

        StructuredTextHtmlPrinter stp = new StructuredTextHtmlPrinter();
        stp.setPrintComments(true);
        stp.preamble();
        for (TopLevelElement e : blocks) {
            e.visit(stp);
            e.visit(s);
        }
        stp.closeHtml();
        FileUtils.writeStringToFile(new File("s01.html"), stp.getString());

        System.out.println(s.getString());


        //System.out.printf(stp.getString());
    }

}
