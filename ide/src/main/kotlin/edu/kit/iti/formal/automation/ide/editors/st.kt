package edu.kit.iti.formal.automation.ide.editors

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.ide.*
import edu.kit.iti.formal.automation.ide.tools.OutlineService
import edu.kit.iti.formal.automation.ide.tools.OverviewStructureNode
import edu.kit.iti.formal.automation.ide.tools.StructureData
import edu.kit.iti.formal.automation.ide.tools.StructureTypeIcon
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Lexer.*
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
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
            PROGRAM,
            INITIAL_STEP,
            TRANSITION,
            END_TRANSITION,
            END_VAR,
            VAR,
            VAR_ACCESS,
            VAR_CONFIG,
            VAR_EXTERNAL,
            VAR_GLOBAL,
            VAR_INPUT,
            VAR_IN_OUT,
            VAR_OUTPUT,
            VAR_TEMP,
            END_PROGRAM,
            END_ACTION,
            END_CASE,
            END_CLASS,
            END_CONFIGURATION,
            END_FUNCTION_BLOCK,
            FUNCTION_BLOCK,
            IEC61131Lexer.FUNCTION,
            END_FUNCTION,
            END_INTERFACE,
            END_METHOD,
            INTERFACE,
            METHOD,
            END_NAMESPACE,
            NAMESPACE,
            END_STEP,
            STEP,
            TYPE,
            END_TYPE,
            STRUCT, END_STRUCT,
            CONFIGURATION, END_CONFIGURATION,
            ACTION, END_ACTION)

    private val DATATYPE_KEYWORD = setOf(
            ANY_BIT,
            ARRAY,
            STRING,
            WSTRING,
            ANY_DATE,
            ANY_INT,
            ANY_NUM,
            ANY_REAL,
            REAL,
            LREAL,
            INT,
            DINT,
            UDINT,
            SINT,
            USINT,
            ULINT,
            DINT,
            LINT,
            DATE,
            DATE_AND_TIME,
            TIME,
            WORD,
            LWORD,
            DWORD,
            BOOL)

    private val LITERALS = setOf(
            DATE_LITERAL,
            INTEGER_LITERAL,
            BITS_LITERAL,
            CAST_LITERAL,
            DIRECT_VARIABLE_LITERAL,
            REAL_LITERAL,
            STRING_LITERAL,
            TOD_LITERAL,
            TIME_LITERAL,
            WSTRING_LITERAL
    )

    val CONTROL_KEYWORDS = setOf(
            IF, ELSE, ELSEIF, FOR, END_FOR,
            WHILE, END_WHILE, REPEAT, END_REPEAT,
            END_IF, DO, THEN, UNTIL, TO,
            WITH, CASE, END_CASE, OF
    )

    val OPERATORS = setOf(
            NOT, AND, OR, MOD, DIV, MULT, MINUS, EQUALS, NOT_EQUALS,
            GREATER_EQUALS, GREATER_THAN, LESS_EQUALS, LESS_THAN,
            IL_ADD, IL_ANDN, IL_CAL, IL_CALC, IL_CALCN, IL_CD, IL_CLK,
            IL_CU, IL_DIV, IL_EQ, IL_GE, IL_GT, IL_IN, IL_JMP, IL_JMPC, IL_JMPCN, IL_LD, IL_LDN, IL_LE, IL_LT,
            IL_MOD, IL_MUL, IL_NE, IL_NOT, IL_ORN, IL_PT, IL_PV, IL_R1, IL_R, IL_RET, IL_RETC, IL_RETCN,
            IL_S1, IL_S, IL_ST, IL_STN, IL_STQ, IL_SUB, IL_XORN, IL_OR
    )

    override fun getStyle(index: Int): Style {
        return when (index) {
            in STRUCTURAL_KEYWORDS -> colors.structural
            in CONTROL_KEYWORDS -> colors.control
            in LITERALS -> colors.literal
            in DATATYPE_KEYWORD -> colors.types
            in OPERATORS -> colors.operators
            IDENTIFIER -> colors.identifier
            COMMENT -> colors.comment
            LINE_COMMENT -> colors.comment
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
