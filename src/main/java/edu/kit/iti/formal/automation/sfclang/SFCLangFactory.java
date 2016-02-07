package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import org.antlr.v4.runtime.*;

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

/**
 * Created by weigl on 07.02.16.
 */
public class SFCLangFactory {

    public static SFCDeclaration parse(String filename) throws IOException {
        CharStream cs = new ANTLRFileStream(filename);
        return parse(cs);
    }

    public static SFCDeclaration parse(Reader reader) throws IOException {
        CharStream cs = new ANTLRInputStream(reader);
        return parse(cs);
    }

    public static SFCDeclaration parse(CharStream cs) {
        IEC61131Lexer lexer = new IEC61131Lexer(cs);
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));

        parser.setBuildParseTree(true);
        parser.setTrace(true);

        return parser.start_sfc().ast;
    }


    public static SFCDeclaration parse(InputStream stream) throws IOException {
        CharStream cs = new ANTLRInputStream(stream);
        return parse(cs);

    }
}
