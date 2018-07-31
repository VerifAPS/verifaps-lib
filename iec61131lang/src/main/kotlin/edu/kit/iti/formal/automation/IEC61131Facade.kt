package edu.kit.iti.formal.automation

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.analysis.*
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.ast.Top
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.automation.visitors.Visitable
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.*
import java.nio.charset.Charset
import java.nio.file.Path

/**
 *
 * IEC61131Facade class.
 *
 * @author Alexander Weigl
 * @version 1
 * @since 27.11.16
 */
object IEC61131Facade {
    /**
     * Parse the given string into an expression.
     *
     * @param input an expression in Structured Text
     * @return The AST of the Expression
     */
    fun expr(input: CharStream): Expression {
        val parser = getParser(input)
        val ctx = parser.expression()
        val expr = ctx.accept(IECParseTreeToAST()) as Expression
        parser.errorReporter.throwException()
        return expr
    }

    fun getParser(input: CharStream): IEC61131Parser {
        val lexer = IEC61131Lexer(input)
        val p = IEC61131Parser(CommonTokenStream(lexer))
        p.errorListeners.clear()
        p.addErrorListener(p.errorReporter)
        //   p.errorHandler = BailErrorStrategy()
        return p
    }

    fun expr(input: String): Expression {
        return expr(CharStreams.fromString(input))
    }

    /**
     * Return the textual representation of the given AST.
     *
     * @param ast a [edu.kit.iti.formal.automation.st.ast.Top] object.
     * @return a [java.lang.String] object.
     */
    fun print(ast: Top, comments: Boolean = true): String {
        val sw = StringWriter()
        printTo(sw, ast, comments)
        return sw.toString()
    }

    fun printTo(stream: Writer, ast: Top, comments: Boolean = false) {
        val stp = StructuredTextPrinter(CodeWriter(stream))
        stp.isPrintComments = comments
        ast.accept(stp)
    }


    /**
     *
     * statements.
     */
    fun statements(input: CharStream): StatementList {
        val parser = getParser(input)
        val stmts = parser.statement_list().accept(IECParseTreeToAST()) as StatementList
        parser.errorReporter.throwException()
        return stmts
    }

    fun statements(input: String): StatementList {
        return statements(CharStreams.fromString(input))
    }

    fun file(input: CharStream): PouElements {
        val parser = getParser(input)
        val tle = parser.start().accept(IECParseTreeToAST()) as PouElements
        parser.errorReporter.throwException()
        return tle
    }

    @Throws(IOException::class)
    fun file(s: Path): PouElements {
        return file(CharStreams.fromPath(s))
    }

    @Throws(IOException::class)
    fun file(f: File): PouElements {
        return file(f.toPath())
    }

    fun resolveDataTypes(elements: PouElements, scope: Scope = Scope.defaultScope()): Scope {
        val fdt = RegisterDataTypes(scope)
        val rdt = ResolveDataTypes(scope)
        //val rr = ResolveReferences(scope)
        elements.accept(fdt)
        elements.accept(rdt)
        elements.accept(rdt)

        elements.accept(RewriteEnums)
        elements.accept(MaintainInitialValues())

        //elements.accept(rr)
        return scope
    }

    fun resolveDataTypes(scope: Scope = Scope.defaultScope(), vararg elements: Visitable): Scope {
        val fdt = RegisterDataTypes(scope)
        val rdt = ResolveDataTypes(scope)
        //val rr = ResolveReferences(scope)
        elements.forEach { it.accept(fdt) }
        elements.forEach { it.accept(rdt) }
        elements.forEach { it.accept(RewriteEnums) }
        elements.forEach { it.accept(MaintainInitialValues()) }
        //elements.accept(rr)
        return scope
    }


    fun getParser(s: String): IEC61131Parser {
        return getParser(CharStreams.fromString(s))
    }

    fun file(resource: InputStream) = file(CharStreams.fromStream(resource, Charset.defaultCharset()))

    fun filer(input: CharStream, builtins: Boolean = false): Pair<PouElements, List<ReporterMessage>> {
        val p = file(input)
        if (builtins)
            p.addAll(BuiltinLoader.loadDefault())
        resolveDataTypes(p)
        return p to check(p)
    }

    fun filer(input: File, builtins: Boolean = false) = filer(CharStreams.fromFileName(input.absolutePath), builtins)

    fun check(p: PouElements): MutableList<ReporterMessage> {
        val r = CheckForTypes.DefaultReporter()
        p.accept(CheckForTypes(r))
        return r.messages
    }

}

