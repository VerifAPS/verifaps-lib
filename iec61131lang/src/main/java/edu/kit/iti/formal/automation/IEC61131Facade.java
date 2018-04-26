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

import edu.kit.iti.formal.automation.analysis.*;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.jetbrains.annotations.NotNull;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;

/**
 * <p>IEC61131Facade class.</p>
 *
 * @author Alexander Weigl
 * @version 1
 * @since 27.11.16
 */
public class IEC61131Facade {
    /**
     * Parse the given string into an expression.
     *
     * @param input an expression in Structured Text
     * @return The AST of the Expression
     */
    public static Expression expr(CharStream input) {
        IEC61131Parser parser = getParser(input);
        IEC61131Parser.ExpressionContext ctx = parser.expression();
        return (Expression) ctx.accept(new IECParseTreeToAST());
    }

    @NotNull
    public static IEC61131Parser getParser(CharStream input) {
        IEC61131Lexer lexer = new IEC61131Lexer(input);
        return new IEC61131Parser(new CommonTokenStream(lexer));
    }

    public static Expression expr(String input) {
        return expr(CharStreams.fromString(input));
    }

    /**
     * Return the textual representation of the given AST.
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @return a {@link java.lang.String} object.
     */
    public static String print(Top ast) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        //stp.setPrintComments(true);
        ast.accept(stp);
        return stp.getString();
    }

    public static String print(StatementList ast) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        ast.forEach(s -> s.accept(stp));
        return stp.getString();
    }

    /**
     * <p>statements.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public static StatementList statements(CharStream input) {
        IEC61131Parser parser = getParser(input);
        return (StatementList) parser.statement_list().accept(new IECParseTreeToAST());
    }

    public static StatementList statements(String input) {
        return statements(CharStreams.fromString(input));
    }


    /**
     * <p>file.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
     */
    public static TopLevelElements file(CharStream input) {
        IEC61131Parser parser = getParser(input);
        return (TopLevelElements) parser.start().accept(new IECParseTreeToAST());
    }

    public static TopLevelElements file(Path s) throws IOException {
        return file(CharStreams.fromPath(s));
    }

    public static TopLevelElements file(File f) throws IOException {
        return file(f.toPath());
    }

    /**
     * <p>resolveDataTypes.</p>
     *
     * @param elements a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
     * @return a {@link edu.kit.iti.formal.automation.scope.GlobalScope} object.
     */
    public static GlobalScope resolveDataTypes(TopLevelElements elements) {
        GlobalScope scope = GlobalScope.defaultScope();
        FindDataTypes fdt = new FindDataTypes(scope);
        ResolveDataTypes rdt = new ResolveDataTypes(scope);
        ResolveReferences rr = new ResolveReferences(scope);
        elements.accept(fdt);
        elements.accept(rdt);
        elements.accept(rr);
        return scope;
    }

    /**
     * Find all instances of classes and FBs belonging to the given top level element..
     * @param element The top level element to visit.
     * @param globalScope Global scope after data types have been resolved.
     * @return The instance scope containing all instances.
     */
    public static InstanceScope findInstances(@NotNull TopLevelElement element, @NotNull GlobalScope globalScope) {
        InstanceScope instanceScope = new InstanceScope(globalScope);
        element.accept(new FindInstances(instanceScope));
        return instanceScope;
    }

    private static final int FIND_EFFECTIVE_SUBTYPES_LIMIT = 1000;

    public static EffectiveSubtypeScope findEffectiveSubtypes(TopLevelElements topLevelElements,
                                                              GlobalScope globalScope, InstanceScope instanceScope) {
        FindEffectiveSubtypes findEffectiveSubtypes = new FindEffectiveSubtypes(globalScope, instanceScope);
        int i;
        for (i = 0; i < FIND_EFFECTIVE_SUBTYPES_LIMIT && !findEffectiveSubtypes.fixpointReached(); i++) {
            findEffectiveSubtypes.prepareRun();
            topLevelElements.accept(findEffectiveSubtypes);
        }
        System.out.println("Done: fixpoint is " + findEffectiveSubtypes.fixpointReached() + " after " + i + " steps");
        return findEffectiveSubtypes.getEffectiveSubtypeScope();
    }

    public static IEC61131Parser getParser(String s) {
        return getParser(CharStreams.fromString(s));
    }
}
