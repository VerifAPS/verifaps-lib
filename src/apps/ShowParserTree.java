package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextLexer;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextParser;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
//import org.antlr.v4.runtime.tree.gui.TreeViewer;

import javax.swing.*;
import java.io.IOException;
import java.util.Arrays;


/**
 * Created by weigla on 07.06.2014.
 */
@Parameters(commandNames = "spt", commandDescription = "show parse tree", separators = "=")
public class ShowParserTree extends App {

    @Parameter(names = "--file", required = true)
    public String file;

    public void execute() throws IOException {
        showParseTree(file);
    }

    private static void showParseTree(String def) throws IOException {
        StructuredTextLexer stl = new StructuredTextLexer(new ANTLRFileStream(def));
        CommonTokenStream cts = new CommonTokenStream(stl);
        StructuredTextParser stp = new StructuredTextParser(cts);
        stp.setBuildParseTree(true);
        stp.setTrimParseTree(true);
        stp.setBuildParseTree(true);
        ParseTree pt = stp.statement_list();

        //show AST in GUI
        JFrame frame = new JFrame("Antlr AST");
        JPanel panel = new JPanel();
        //TreeViewer viewr = new TreeViewer(Arrays.asList(
                //stp.getRuleNames()), pt);
        //viewr.setScale(1.5);//scale a little
        //panel.add(viewr);
        frame.add(panel);
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        frame.setSize(200, 200);
        frame.setVisible(true);
    }
}
