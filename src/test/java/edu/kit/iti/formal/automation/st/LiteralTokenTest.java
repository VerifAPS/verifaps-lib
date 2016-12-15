package edu.kit.iti.formal.automation.st;

import edu.kit.iti.formal.automation.TestUtils;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Collection;
import java.util.List;

/**
 * Created by weigl on 15.12.16.
 */
@RunWith(Parameterized.class)
public class LiteralTokenTest {
    static String[] CASES = new String[]{
            //"LWORD#2#22020",
            "47474.759",
            "LWORD#2#11010",
            "0.456_262",
            "1.34E-12",
            "1e1",
            "1.34e1",
            "T#5d14h12m18s5ms",
            "T#5d_14h_12m_18s_5ms",
            "TIME#5d_14h_12m_5ms",
    };

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> data() {
        return TestUtils.asParameters(CASES);
    }

    @Parameterized.Parameter(0)
    public String expr;

    @Test
    public void testTokens() {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(expr));
        List<? extends Token> toks = lexer.getAllTokens();
        System.out.println(toks);
        Assert.assertEquals(1, toks.size());
    }
}
