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

import edu.kit.iti.formal.automation.analysis.FindDataTypes;
import edu.kit.iti.formal.automation.analysis.FindEffectiveSubtypes;
import edu.kit.iti.formal.automation.analysis.FindInstances;
import edu.kit.iti.formal.automation.analysis.ResolveDataTypes;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;
import lombok.val;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

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
    private static final int FIND_EFFECTIVE_SUBTYPES_LIMIT = 1000;

    /**
     * Parse the given string into an expression.
     *
     * @param input an expression in Structured Text
     * @return The AST of the Expression
     */
    public static Expression expr(CharStream input) {
        IEC61131Parser parser = getParser(input);
        IEC61131Parser.ExpressionContext ctx = parser.expression();
        val expr = (Expression) ctx.accept(new IECParseTreeToAST());
        parser.getErrorReporter().throwException();
        return expr;
    }

    @NotNull
    public static IEC61131Parser getParser(CharStream input) {
        IEC61131Lexer lexer = new IEC61131Lexer(input);
        IEC61131Parser p = new IEC61131Parser(new CommonTokenStream(lexer));
        p.getErrorListeners().clear();
        p.addErrorListener(p.getErrorReporter());
        return p;
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
    public static String print(Top ast, boolean comments) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        stp.setPrintComments(comments);
        ast.accept(stp);
        return stp.getString();
    }

    public static String print(StatementList statements) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        statements.accept(stp);
        return stp.getString();
    }


    @Nullable
    public static String print(@Nullable Top top) {
        return print(top, false);
    }

    /**
     * <p>statements.</p>
     */
    public static StatementList statements(CharStream input) {
        IEC61131Parser parser = getParser(input);
        val stmts = (StatementList) parser.statement_list().accept(new IECParseTreeToAST());
        parser.getErrorReporter().throwException();
        return stmts;
    }

    public static StatementList statements(String input) {
        return statements(CharStreams.fromString(input));
    }

    public static TopLevelElements file(CharStream input) {
        IEC61131Parser parser = getParser(input);
        TopLevelElements tle = (TopLevelElements) parser.start().accept(new IECParseTreeToAST());
        parser.getErrorReporter().throwException();
        return tle;
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
     * @return a {@link edu.kit.iti.formal.automation.scope.Scope} object.
     */
    public static Scope resolveDataTypes(TopLevelElements elements) {
        Scope scope = Scope.defaultScope();
        FindDataTypes fdt = new FindDataTypes(scope);
        ResolveDataTypes rdt = new ResolveDataTypes(scope);
        //ResolveReferences rr = new ResolveReferences(scope);
        elements.accept(fdt);
        elements.accept(rdt);
        //elements.accept(rr);
        return scope;
    }

    /**
     * Find all instances of classes and FBs belonging to the given top level element..
     *
     * @param element     The top level element to visit.
     * @param globalScope Global scope after data types have been resolved.
     * @return The instance scope containing all instances.
     */
    public static InstanceScope findInstances(@NotNull TopLevelElement element, @NotNull Scope globalScope) {
        InstanceScope instanceScope = new InstanceScope(globalScope);
        element.accept(new FindInstances(instanceScope));
        return instanceScope;
    }

    public static void findEffectiveSubtypes(TopLevelElements topLevelElements, Scope globalScope,
                                             InstanceScope instanceScope) {
        FindEffectiveSubtypes findEffectiveSubtypes = new FindEffectiveSubtypes(globalScope, instanceScope);
        int i;
        for (i = 0; i < FIND_EFFECTIVE_SUBTYPES_LIMIT && !findEffectiveSubtypes.fixpointReached(); i++) {
            findEffectiveSubtypes.prepareRun();
            topLevelElements.accept(findEffectiveSubtypes);
        }
        System.out.println("Done: fixpoint is " + findEffectiveSubtypes.fixpointReached() + " after " + i + " steps");
    }
    
    public static IEC61131Parser getParser(String s) {
        return getParser(CharStreams.fromString(s));
    }

}
