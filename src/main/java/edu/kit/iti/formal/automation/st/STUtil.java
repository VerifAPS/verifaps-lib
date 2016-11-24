package edu.kit.iti.formal.automation.st;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.Expression;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

/**
 * Created by weigl on 24.11.16.
 */
public class STUtil {
    public static Expression expr(String str) {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(str));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        return parser.expression().ast;
    }
}
