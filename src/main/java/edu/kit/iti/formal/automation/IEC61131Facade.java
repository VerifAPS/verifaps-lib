package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

/**
 * @author Alexander Weigl
 * @version 1 (27.11.16)
 */
public class IEC61131Facade {
    /**
     * Parse the given string into an expression.
     * @param str an expression in Structured Text
     * @return The AST of the Expression
     */
    public static Expression expr(String str) {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(str));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        return parser.expression().ast;
    }

    /**
     * Return the textual representation of the given AST.
     * @param ast
     * @return
     */
    public static String print(Top ast) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        ast.visit(stp);
        return stp.getString();
    }

    /**
     *
     * @param str
     * @return
     */
    public static StatementList statements(String str) {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(str));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        return parser.statement_list().ast;
    }


    public static TopLevelElements file(String str) {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(str));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        return new TopLevelElements(parser.start().ast);
    }

    public static GlobalScope resolveDataTypes(TopLevelElements elements) {
        return ResolveDataTypes.resolve(elements);
    }


}
