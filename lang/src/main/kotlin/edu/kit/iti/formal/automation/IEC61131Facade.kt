package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.analysis.*
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.il.IlBody
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.TranslationSfcToStOld
import edu.kit.iti.formal.automation.st.TranslationSfcToStPipeline
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.warn
import org.antlr.v4.runtime.*
import java.io.*
import java.nio.charset.Charset
import java.nio.file.Path
import java.util.*

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


    fun file(path: Path, tee: File? = null): PouElements {
        return if (path.endsWith("xml")) {
            val out = IECXMLFacade.extractPLCOpenXml(path)
            if (tee != null) {
                tee.bufferedWriter().use {
                    it.write(out)
                }
                file(tee)
            } else {
                file(CharStreams.fromString(out, path.toString()))
            }
        } else
            file(CharStreams.fromPath(path))
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
        //val oo = ResolveOO(scope)
        //val rr = ResolveReferences(scope)
        elements.accept(EnsureFunctionReturnValue)
        elements.accept(fdt)
        elements.accept(rdt)
        elements.accept(RewriteEnums)
        elements.accept(MaintainInitialValues())
        //elements.accept(oo)
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
        val seq = LinkedList<PouElement>()
        input.parallelStream().forEach { synchronized(seq) { seq.addAll(file(it)) } }
        val p = PouElements(seq)
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
    fun readProgramsWLN(libraryElements: List<File>, programs: List<File>, names: List<String>)
            : List<PouExecutable?> {
        val selectors = names.map { name ->
            { elements: PouElements -> elements.find { it.name == name } as PouExecutable? }
        }
        return readProgramsWLS(libraryElements, programs, selectors)
    }

    /**
     * Read programs with support for common libraries and a selection either by name or PROGRAM_DECLARATION
     */
    fun readProgramsWLPN(libraryElements: List<File>, programs: List<String>)
            : List<PouExecutable?> {
        val p = programs.map {
            if ('@' in it) {
                val a = it.split('@', limit = 2)
                a[0] to a[1]
            } else {
                null to it
            }
        }
        val pfiles = p.map { (_, a) -> File(a) }
        val selectors = p.map { (name, _) ->
            if (name == null)
                { elements: PouElements -> Utils.findProgram(elements) }
            else
                { elements: PouElements -> elements.find { it.name == name } as PouExecutable? }
        }
        return readProgramsWLS(libraryElements, pfiles, selectors)
    }


    /**
     *
     */
    fun readProgramsWLS(libraryElements: List<File>,
                        programs: List<File>,
                        selectors: List<(PouElements) -> PouExecutable?>)
            : List<PouExecutable?> {
        return programs.zip(selectors).map { (it, selector) ->
            val (elements, error) = filefr(libraryElements + it)
            error.forEach { warn(it.toHuman()) }
            selector(elements)
        }
    }


    /**
     *
     */
    fun readProgramsWLP(libraryElements: List<File>, programs: List<File>): List<PouExecutable?> =
            readProgramsWLS(libraryElements, programs,
                    programs.map { _ -> Utils::findProgram })


    /**
     *
     */
    fun check(p: PouElements): MutableList<ReporterMessage> {
        val r = Reporter()
        getCheckers(r).forEach { p.accept(it) }
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

    //region translations
    fun translateSfcToSt(scope: Scope, sfc: SFCImplementation,
                         name: String = "", old: Boolean = false): StatementList {
        val st = StatementList()
        sfc.networks.forEachIndexed { index, network ->
            val element = if (old) TranslationSfcToStOld(network, name, index, scope)
            else TranslationSfcToStPipeline(network, name, index, scope)
            st.add(element.call())
        }
        return st
    }

    fun translateSfc(elements: PouElements) {
        elements.forEach { it.accept(TranslateSfcToSt) }
    }


    fun translateFbd(elements: PouElements) {
        elements.forEach { it.accept(TranslateFbdToSt) }
    }
    //endregion


    object InstructionList {
        /*
        fun getParser(input: Token): IlParser {
            return getParser(
                    CharStreams.fromString(input.text),
                    ShiftedTokenFactory(input))
        }
        fun getParser(input: CharStream, position: Position): IlParser {
            return getParser(input, ShiftedTokenFactory(position))
        }
        fun getParser(input: CharStream, tokenFactory: TokenFactory<*>? = null): IlParser {
            val lexer = IlLexer(input)
            if (tokenFactory != null)
                lexer.tokenFactory = tokenFactory
            val p = IlParser(CommonTokenStream(lexer))
            p.errorListeners.clear()
            p.addErrorListener(p.errorReporter)
            return p
        }
        fun parseBody(token: Token): IlBody {
            val ctx = getParser(token).ilBody()
            return ctx.accept(IlTransformToAst()) as IlBody
        }
        */


        fun parseBody(token: String): IlBody {
            val lexer = IEC61131Lexer(CharStreams.fromString(token))
            lexer.pushMode(1)
            val parser = IEC61131Parser(CommonTokenStream(lexer))
            val ctx = parser.ilBody()
            return ctx.accept(IECParseTreeToAST()) as IlBody
        }

        private class ShiftedTokenFactory(val offset: Int = 0,
                                          val offsetLine: Int = 0,
                                          val offsetChar: Int = 0) : CommonTokenFactory() {
            constructor(position: Position) : this(position.offset, position.lineNumber, position.charInLine)
            constructor(token: Token) : this(token.startIndex, token.line, token.charPositionInLine)

            override fun create(source: org.antlr.v4.runtime.misc.Pair<TokenSource, CharStream>?, type: Int, text: String?, channel: Int, start: Int, stop: Int, line: Int, charPositionInLine: Int): CommonToken {
                val token = super.create(source, type, text, channel, start, stop, line, charPositionInLine)
                token.startIndex += offset
                token.stopIndex += offset
                token.charPositionInLine += offsetChar
                token.line += offsetLine
                return token
            }
        }
    }
}