package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.Token;
import org.junit.Test;

/**
 * Created by weigl on 07.02.16.
 */
public class TokenTest {
    @Test public void sfcTok() {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream("SFC"));
        for (Token t:
             lexer.getAllTokens()) {
            System.out.println(t.getType());
        }
    }
}
