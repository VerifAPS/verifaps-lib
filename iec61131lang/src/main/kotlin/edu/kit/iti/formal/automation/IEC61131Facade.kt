package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.analysis.*
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.util.CodeWriter
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.*
import java.nio.charset.Charset

/**
 * IEC61131Facade class.
 * @author Alexander Weigl
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

    fun expr(input: String): Expression {
        return expr(CharStreams.fromString(input))
    }

    fun getParser(input: CharStream): IEC61131Parser {
        val lexer = IEC61131Lexer(input)
        val p = IEC61131Parser(CommonTokenStream(lexer))
        p.errorListeners.clear()
        p.addErrorListener(p.errorReporter)
        return p
    }

    fun statements(input: CharStream): StatementList {
        val parser = getParser(input)
        val stmts = parser.statement_list().accept(IECParseTreeToAST()) as StatementList
        parser.errorReporter.throwException()
        return stmts
    }

    fun statements(input: String): StatementList = statements(CharStreams.fromString(input))

    fun file(input: CharStream): PouElements {
        val parser = getParser(input)
        val tle = parser.start().accept(IECParseTreeToAST()) as PouElements
        parser.errorReporter.throwException()
        return tle
    }


    @Throws(IOException::class)
    fun file(f: File, teeXmlParser: Boolean = true): PouElements {
        return if (f.extension == "xml") {
            val out = IECXMLFacade.extractPLCOpenXml(f.absolutePath)
            if (teeXmlParser) {
                val stfile = File(f.parentFile, f.nameWithoutExtension + ".st")
                stfile.bufferedWriter().use {
                    it.write(out)
                }
                file(CharStreams.fromFileName(stfile.absolutePath))
            } else {
                file(CharStreams.fromString(out, f.absolutePath))
            }
        } else
            file(CharStreams.fromFileName(f.absolutePath))

    }

    fun file(resource: InputStream) = file(CharStreams.fromStream(resource, Charset.defaultCharset()))

    fun getParser(s: String): IEC61131Parser {
        return getParser(CharStreams.fromString(s))
    }

    fun resolveDataTypes(elements: PouElements, scope: Scope = Scope.defaultScope()): Scope {
        val fdt = RegisterDataTypes(scope)
        val rdt = ResolveDataTypes(scope)
        //val rr = ResolveReferences(scope)
        elements.accept(fdt)
        elements.accept(EnsureFunctionReturnValue)

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

    fun fileResolve(input: List<CharStream>, builtins: Boolean = false): Pair<PouElements, List<ReporterMessage>> {
        val p = PouElements()
        input.forEach { p.addAll(file(it)) }
        if (builtins)
            p.addAll(BuiltinLoader.loadDefault())
        resolveDataTypes(p)
        return p to check(p)
    }

    fun fileResolve(input: CharStream, builtins: Boolean = false): Pair<PouElements, List<ReporterMessage>> = fileResolve(listOf(input), builtins)

    fun fileResolve(input: File, builtins: Boolean = false) = fileResolve(CharStreams.fromFileName(input.absolutePath), builtins)

    fun filefr(inputs: List<File>, builtins: Boolean = false) =
            fileResolve(inputs.map { CharStreams.fromFileName(it.absolutePath) }, builtins)


    /**
     *
     */
    fun readProgramsWithLibrary(libraryElements: List<File>, programs: List<File>): List<PouExecutable?> =
            readProgramsWithLibrary(libraryElements, programs, Utils::findProgram)


    /**
     *
     */
    fun readProgramsWithLibrary(libraryElements: List<File>, programs: List<File>, select: String): List<PouExecutable?> =
            readProgramsWithLibrary(libraryElements, programs) { seq ->
                seq.find { it.name == select } as? PouExecutable
            }

    /**
     *
     */
    fun readProgramsWithLibrary(libraryElements: List<File>,
                                programs: List<File>,
                                selector: (PouElements) -> PouExecutable?)
            : List<PouExecutable?> {
        return programs.map {
            val (elements, error) = IEC61131Facade.filefr(libraryElements + it)
            error.forEach { Console.warn(it.toHuman()) }
            selector(elements)
        }
    }

    /**
     *
     */
    fun check(p: PouElements): MutableList<ReporterMessage> {
        val r = CheckForTypes.DefaultReporter()
        p.accept(CheckForTypes(r))
        return r.messages
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

}

