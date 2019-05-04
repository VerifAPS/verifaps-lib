package edu.kit.iti.formal.automation.ide.editors

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.ide.*
import edu.kit.iti.formal.automation.ide.tools.OutlineService
import edu.kit.iti.formal.automation.ide.tools.OverviewStructureNode
import edu.kit.iti.formal.automation.ide.tools.StructureData
import edu.kit.iti.formal.automation.ide.tools.StructureTypeIcon
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import me.tomassetti.kanvas.AntlrLexerFactory
import me.tomassetti.kanvas.BaseLanguageSupport
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.fife.io.DocumentReader
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import org.fife.ui.rsyntaxtextarea.folding.Fold
import org.fife.ui.rsyntaxtextarea.folding.FoldParser
import org.fife.ui.rsyntaxtextarea.folding.FoldType
import org.fife.ui.rsyntaxtextarea.parser.*
import java.util.*
import javax.swing.Icon
import javax.swing.text.BadLocationException

class IECLanguageSupport(lookup: Lookup) : BaseLanguageSupport() {
    override fun createParser(textArea: CodeEditor, lookup: Lookup): Parser? = STChecker(textArea, lookup)

    override val extension: Collection<String> = setOf("st", "iec", "iec61131")
    override val mimeType = "text/iec61131"
    override val syntaxScheme: SyntaxScheme = IEC61131SyntaxScheme(lookup)
    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer =
                    IEC61131Lexer(CharStreams.fromString(code))
        }
}

class IEC61131SyntaxScheme(lookup: Lookup) : SyntaxScheme(true) {
    val colors: Colors by lookup.with()
    private val STRUCTURAL_KEYWORDS = setOf(
            IEC61131Lexer.PROGRAM,
            IEC61131Lexer.INITIAL_STEP,
            IEC61131Lexer.TRANSITION,
            IEC61131Lexer.END_TRANSITION,
            IEC61131Lexer.END_VAR,
            IEC61131Lexer.VAR,
            IEC61131Lexer.VAR_ACCESS,
            IEC61131Lexer.VAR_CONFIG,
            IEC61131Lexer.VAR_EXTERNAL,
            IEC61131Lexer.VAR_GLOBAL,
            IEC61131Lexer.VAR_INPUT,
            IEC61131Lexer.VAR_IN_OUT,
            IEC61131Lexer.VAR_OUTPUT,
            IEC61131Lexer.VAR_TEMP,
            IEC61131Lexer.END_PROGRAM,
            IEC61131Lexer.END_ACTION,
            IEC61131Lexer.END_CASE,
            IEC61131Lexer.END_CLASS,
            IEC61131Lexer.END_CONFIGURATION,
            IEC61131Lexer.END_FUNCTION_BLOCK,
            IEC61131Lexer.FUNCTION_BLOCK,
            FUNCTION,
            IEC61131Lexer.END_FUNCTION,
            IEC61131Lexer.END_INTERFACE,
            IEC61131Lexer.END_METHOD,
            IEC61131Lexer.INTERFACE,
            IEC61131Lexer.METHOD,
            IEC61131Lexer.END_NAMESPACE,
            IEC61131Lexer.NAMESPACE,
            IEC61131Lexer.END_STEP,
            IEC61131Lexer.STEP,
            IEC61131Lexer.STRUCT, IEC61131Lexer.END_STRUCT,
            IEC61131Lexer.CONFIGURATION, IEC61131Lexer.END_CONFIGURATION,
            IEC61131Lexer.ACTION, IEC61131Lexer.END_ACTION)

    private val DATATYPE_KEYWORD = setOf(
            IEC61131Lexer.ANY_BIT,
            IEC61131Lexer.ARRAY,
            IEC61131Lexer.STRING,
            IEC61131Lexer.WSTRING,
            IEC61131Lexer.ANY_DATE,
            IEC61131Lexer.ANY_INT,
            IEC61131Lexer.ANY_NUM,
            IEC61131Lexer.ANY_REAL,
            IEC61131Lexer.REAL,
            IEC61131Lexer.LREAL,
            IEC61131Lexer.INT,
            IEC61131Lexer.DINT,
            IEC61131Lexer.UDINT,
            IEC61131Lexer.SINT,
            IEC61131Lexer.USINT,
            IEC61131Lexer.ULINT,
            IEC61131Lexer.DINT,
            IEC61131Lexer.LINT,
            IEC61131Lexer.DATE,
            IEC61131Lexer.DATE_AND_TIME,
            IEC61131Lexer.TIME,
            IEC61131Lexer.WORD,
            IEC61131Lexer.LWORD,
            IEC61131Lexer.DWORD,
            IEC61131Lexer.BOOL)

    private val LITERALS = setOf(
            IEC61131Lexer.DATE_LITERAL,
            IEC61131Lexer.INTEGER_LITERAL,
            IEC61131Lexer.BITS_LITERAL,
            IEC61131Lexer.CAST_LITERAL,
            IEC61131Lexer.DIRECT_VARIABLE_LITERAL,
            IEC61131Lexer.REAL_LITERAL,
            IEC61131Lexer.STRING_LITERAL,
            IEC61131Lexer.TOD_LITERAL,
            IEC61131Lexer.TIME_LITERAL,
            IEC61131Lexer.WSTRING_LITERAL
    )

    val CONTROL_KEYWORDS = setOf(
            IEC61131Lexer.IF, IEC61131Lexer.ELSE, IEC61131Lexer.ELSEIF, IEC61131Lexer.FOR, IEC61131Lexer.END_FOR, IEC61131Lexer.WHILE, IEC61131Lexer.END_WHILE, IEC61131Lexer.REPEAT, IEC61131Lexer.END_REPEAT,
            IEC61131Lexer.DO, IEC61131Lexer.THEN, IEC61131Lexer.UNTIL, IEC61131Lexer.TO, IEC61131Lexer.WITH, IEC61131Lexer.CASE, IEC61131Lexer.END_CASE, IEC61131Lexer.OF
    )

    override fun getStyle(index: Int): Style {
        return when (index) {
            in STRUCTURAL_KEYWORDS -> colors.structural
            in CONTROL_KEYWORDS -> colors.control
            in LITERALS -> colors.literal
            in DATATYPE_KEYWORD -> colors.types
            IDENTIFIER -> colors.identifier
            IEC61131Lexer.COMMENT -> colors.comment
            IEC61131Lexer.LINE_COMMENT -> colors.comment
            ERROR_CHAR -> colors.error
            else -> colors.default
        }
    }
}

class STChecker(val codeEditor: CodeEditor, val lookup: Lookup) : AbstractParser() {
    val result = DefaultParseResult(this)
    override fun parse(doc: RSyntaxDocument, style: String): ParseResult {
            result.clearNotices()
        val input = DocumentReader(doc)
        val stream = CharStreams.fromReader(input, codeEditor.titleText)
        try {
            val (elements, issues) = IEC61131Facade.fileResolve(stream, false)
            lookup.get<OutlineService>().show(StOverviewTransformer(codeEditor).create(elements))
            issues.forEach {
                result.addNotice(DefaultParserNotice(this, it.message,
                        it.startLine, it.startOffset, it.length))
            }
            lookup.get<ProblemList>().set(codeEditor, issues)
        } catch (e: SyntaxErrorReporter.ParserException) {
            e.errors.forEach {
                result.addNotice(DefaultParserNotice(this, it.msg,
                        it.line, it.offendingSymbol?.startIndex ?: -1,
                        it.offendingSymbol?.text?.length ?: -1))
            }
        } catch (e: Exception) {
        }
        return result
    }

    override fun isEnabled(): Boolean = true
}

class STFoldParser : FoldParser {
    private val OPEN_KEYWORDS =
            regex(hashMapOf("\\bTHEN\\b" to "\\bEND_IF\\b",
                    "\\bFUNCTION\\b" to "\\bEND_FUNCTION\\b",
                    "\\bFUNCTION_BLOCK\\b" to "\\bEND_FUNCTION_BLOCK\\b",
                    "\\bCLASS\\b" to "\\bEND_CLASS\\b",
                    "\\bMETHOD\\b" to "\\bEND_METHOD\\b",
                    "\\bFOR\\b" to "\\bEND_FOR\\b",
                    "\\bWHILE\\b" to "\\bEND_WHILE\\b",
                    "\\bVAR.*\\b" to "\\bEND_VAR\\b",
                    "\\bACTION.*\\b" to "\\bEND_ACTION\\b",
                    "\\bSTEP.*\\b" to "\\bEND_STEP\\b",
                    "\\bPROGRAM\\b" to "\\bEND_PROGRAM\\b"
            ))

    private fun regex(map: HashMap<String, String>): List<Pair<Regex, Regex>> = map.map { (k, v) ->
        k.toRegex(RegexOption.IGNORE_CASE) to v.toRegex(RegexOption.IGNORE_CASE)
    }

    override fun getFolds(textArea: RSyntaxTextArea): List<Fold> {
        val folds = ArrayList<Fold>()
        val expected = LinkedList<Pair<Regex, Fold>>()


        try {
            var offset = 0
            val lines = textArea.text.splitToSequence('\n')
            lines.forEachIndexed { idx, line ->
                val match = expected.indexOfFirst { (regex, _) ->
                    regex.containsMatchIn(line)
                }

                if (match > -1) {
                    for (i in 0..match) {
                        val (_, f) = expected.pollFirst()
                        f.endOffset = offset
                        folds += f
                    }
                }

                loop@ for ((open, close) in OPEN_KEYWORDS) {
                    when {
                        open.containsMatchIn(line) && close.containsMatchIn(line) -> {
                            val f = Fold(FoldType.CODE, textArea, offset)
                            f.endOffset = offset + line.length
                            expected.addFirst(close to f)
                            break@loop
                        }
                        open.containsMatchIn(line) -> {
                            expected.addFirst(
                                    close to Fold(FoldType.CODE, textArea, offset))
                            break@loop
                        }
                    }
                }

                offset += line.length + 1
            }
        } catch (ble: BadLocationException) {
            ble.printStackTrace()
        }
        return folds
    }
}


class StOverviewTransformer(val editor: CodeEditor) {
    private val colors: Colors by editor.lookup.with()

    companion object {
        private val ICON_SIZE = 12
        private val ROOT_ICON: Icon = IconFontSwing.buildIcon(FontAwesomeRegular.FILE_CODE, ICON_SIZE.toFloat())
        private val ICON_GVL: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_DATATYPES: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_DATATYPE: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_METHOD: Icon? = StructureTypeIcon.buildIcon("m", ICON_SIZE)
        private val ICON_CLASS: Icon? = StructureTypeIcon.buildIcon("c", ICON_SIZE)

        private val ICON_PROGRAM: Icon? = StructureTypeIcon.buildIcon("p", ICON_SIZE)
        private val ICON_FBD: Icon? = StructureTypeIcon.buildIcon("fbd", ICON_SIZE)
        private val ICON_VAR: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_FUNCTION: Icon? = StructureTypeIcon.buildIcon("f", ICON_SIZE)


    }

    fun create(elements: PouElements): OverviewStructureNode {
        val root = OverviewStructureNode(StructureData(editor.titleText.trim('*'), editor, ROOT_ICON))
        val v = Visitor()
        elements.mapNotNull { it.accept(v) }.forEach { root.add(it) }
        return root
    }

    inner class Visitor : AstVisitor<OverviewStructureNode?>() {


        override fun defaultVisit(obj: Any): OverviewStructureNode? = null

        override fun visit(gvlDecl: GlobalVariableListDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData("global variables", editor, ICON_GVL))
            gvlDecl.scope.accept(this)?.seq?.also { node.seq.addAll(it) }
            return node
        }

        override fun visit(programDeclaration: ProgramDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(programDeclaration.name, editor, ICON_PROGRAM))
            val variables = programDeclaration.scope.accept(this)?.seq
            val actions = programDeclaration.actions.mapNotNull { it.accept(this) }
            variables?.also { node.seq.addAll(it) }
            actions.forEach { node.seq.add(it) }
            return node
        }

        override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(functionBlockDeclaration.name, editor, ICON_FBD))
            val variables = functionBlockDeclaration.scope.accept(this)?.seq
            val actions = functionBlockDeclaration.actions.mapNotNull { it.accept(this) }
            variables?.also { seq -> seq.forEach { node.add(it) } }
            actions.forEach { node.add(it) }
            return node
        }

        override fun visit(functionDeclaration: FunctionDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(functionDeclaration.name, editor, ICON_FUNCTION))
            functionDeclaration.scope.accept(this)?.seq?.also { node.seq.addAll(it) }
            return node
        }

        override fun visit(localScope: Scope): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData("Variables", editor, ICON_VAR))
            localScope.mapNotNull { it.accept(this) }.forEach { node.add(it) }
            return node
        }

        override fun visit(typeDeclarations: TypeDeclarations): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData("Data Types", editor,
                    ICON_DATATYPES, typeDeclarations.startPosition))
            typeDeclarations.mapNotNull {
                OverviewStructureNode(StructureData(it.name, editor, ICON_DATATYPE, it.startPosition))
            }
                    .forEach { node.add(it) }
            return node
        }

        override fun visit(clazz: ClassDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(clazz.name, editor,
                    ICON_CLASS, clazz.startPosition))

            val variables = clazz.scope.accept(this)?.seq
            variables?.also { seq -> seq.forEach { node.add(it) } }

            clazz.methods.mapNotNull {
                it.accept(this)
            }.forEach { node.add(it) }

            return node
        }

        override fun visit(variableDeclaration: VariableDeclaration): OverviewStructureNode? {
            return OverviewStructureNode(
                    StructureData("${variableDeclaration.name} : ${variableDeclaration.dataType}",
                            editor, ICON_METHOD, variableDeclaration.startPosition))
        }

        override fun visit(method: MethodDeclaration): OverviewStructureNode? {
            return OverviewStructureNode(StructureData(method.name, editor, ICON_METHOD, method.startPosition))
        }
    }
}
