package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

/**
 * <p>IEC61131Facade class.</p>
 *
 * @author Alexander Weigl
 * @version 1 (27.11.16)
 */
public class IEC61131Facade {
    /**
     * Parse the given string into an expression.
     *
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
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @return a {@link java.lang.String} object.
     */
    public static String print(Top ast) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        ast.visit(stp);
        return stp.getString();
    }

    /**
     * <p>statements.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public static StatementList statements(String str) {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(str));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        return parser.statement_list().ast;
    }


    /**
     * <p>file.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
     */
    public static TopLevelElements file(String str) {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(str));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        return new TopLevelElements(parser.start().ast);
    }

    /**
     * <p>resolveDataTypes.</p>
     *
     * @param elements a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
     * @return a {@link edu.kit.iti.formal.automation.scope.GlobalScope} object.
     */
    public static GlobalScope resolveDataTypes(TopLevelElements elements) {
        return ResolveDataTypes.resolve(elements);
    }


}
