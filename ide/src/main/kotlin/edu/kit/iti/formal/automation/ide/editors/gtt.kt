package edu.kit.iti.formal.automation.ide.editors

import edu.kit.iti.formal.automation.ide.*
import edu.kit.iti.formal.automation.ide.tools.*
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.automation.st.ast.Position
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParserBaseVisitor
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import org.fife.io.DocumentReader
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import org.fife.ui.rsyntaxtextarea.folding.Fold
import org.fife.ui.rsyntaxtextarea.folding.FoldParser
import org.fife.ui.rsyntaxtextarea.folding.FoldType
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice
import org.fife.ui.rsyntaxtextarea.parser.ParseResult
import java.util.*
import javax.swing.Icon

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.03.19)
 */
class TestTableSyntaxScheme(lookup: Lookup) : SyntaxScheme(true) {
    private val colors: Colors by lookup.with()

    private val STRUCTURAL_KEYWORDS = setOf(
            TestTableLanguageLexer.OPTIONS,
            TestTableLanguageLexer.TABLE,
            TestTableLanguageLexer.FUNCTION,
            TestTableLanguageLexer.OF,
            TestTableLanguageLexer.WITH,
            TestTableLanguageLexer.VAR,
            TestTableLanguageLexer.GVAR,
            TestTableLanguageLexer.AS,
            TestTableLanguageLexer.IF,
            TestTableLanguageLexer.FI,
            TestTableLanguageLexer.GROUP,
            TestTableLanguageLexer.ROW,
            TestTableLanguageLexer.INPUT,
            TestTableLanguageLexer.OUTPUT,
            TestTableLanguageLexer.VAR,
            TestTableLanguageLexer.BACKWARD,
            TestTableLanguageLexer.PLAY,
            TestTableLanguageLexer.PAUSE,
            TestTableLanguageLexer.STATE,
            TestTableLanguageLexer.RELATIONAL
    )
    private val SEPS = setOf(
            TestTableLanguageLexer.RBRACE,
            TestTableLanguageLexer.LBRACE,
            TestTableLanguageLexer.RPAREN,
            TestTableLanguageLexer.LPAREN,
            TestTableLanguageLexer.RBRACKET,
            TestTableLanguageLexer.LBRACKET,
            TestTableLanguageLexer.COLON,
            TestTableLanguageLexer.COMMA
    )
    private val LITERALS = setOf(
            TestTableLanguageLexer.INTEGER
    )

    override fun getStyle(index: Int): Style {
        return when (index) {
            in SEPS -> colors.separators
            in STRUCTURAL_KEYWORDS -> colors.structural
            in LITERALS -> colors.literal
            TestTableLanguageLexer.FQ_VARIABLE -> colors.identifier
            IDENTIFIER -> colors.identifier
            TestTableLanguageLexer.COMMENT -> colors.comment
            TestTableLanguageLexer.LINE_COMMENT -> colors.comment
            else -> colors.default
        }
    }
}

class TestTableLanguageSupport(lookup: Lookup) : BaseLanguageSupport() {
    override fun createParser(textArea: CodeEditor, lookup: Lookup) = TTParser(textArea, lookup)
    override val mimeType: String = "text/gtt"
    override val extension: Collection<String> = setOf("gtt", ".tt.txt", ".tt")
    override val syntaxScheme: SyntaxScheme = TestTableSyntaxScheme(lookup)
    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer =
                    TestTableLanguageLexer(CharStreams.fromString(code))
        }
    override val isCodeFoldingEnabled: Boolean
        get() = true

    override fun configure(textArea: RSyntaxTextArea) {
        textArea.paintTabLines = true
        textArea.tabsEmulated = true
    }
}

class TTOverviewTransformer(val editor: CodeEditor) {
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

    fun create(gtt: TestTableLanguageParser.FileContext): OverviewStructureNode {
        val visitor = Visitor()
        return gtt.accept(visitor)!!
    }

    inner class Visitor : TestTableLanguageParserBaseVisitor<OverviewStructureNode?>() {
        override fun visitFile(ctx: TestTableLanguageParser.FileContext): OverviewStructureNode {
            val root = OverviewStructureNode(StructureData(editor.titleText.trim('*'), editor, ROOT_ICON))
            ctx.table().mapAndAddTo(root)
            return root
        }

        override fun visitTable(ctx: TestTableLanguageParser.TableContext): OverviewStructureNode? {
            val name =
                    when (val header = ctx.tableHeader()) {
                        is TestTableLanguageParser.TableHeaderFunctionalContext -> header.name.text
                        is TestTableLanguageParser.TableHeaderRelationalContext -> header.name.text
                        else -> ""
                    }

            val root = OverviewStructureNode(StructureData(name, editor, ROOT_ICON))
            ctx.freeVariable().mapAndAddTo(root)
            ctx.signature().mapAndUnpackTo(root)
            ctx.opts()?.accept(this)?.also { root.add(it) }
            ctx.group().accept(this)?.also { root.add(it) }
            ctx.function().mapAndAddTo(root)
            return root
        }

        override fun visitOpts(ctx: TestTableLanguageParser.OptsContext): OverviewStructureNode {
            val root = OverviewStructureNode(StructureData("Options", editor, ROOT_ICON))
            ctx.kv().forEach {
                val n = OverviewStructureNode(
                        StructureData(it.key.text, editor, ROOT_ICON, Position.start(it.key.start)))
                root.add(n)
            }
            return root
        }

        override fun visitFreeVariable(ctx: TestTableLanguageParser.FreeVariableContext): OverviewStructureNode {
            return OverviewStructureNode(StructureData(ctx.name.text + " : " + ctx.dt.text,
                    editor, null, Position.start(ctx.start)))
        }

        override fun visitSignature(ctx: TestTableLanguageParser.SignatureContext): OverviewStructureNode {
            val root = OverviewStructureNode(StructureData(""))
            //TODO Handle remaining variable cases for relational tables
            ctx.variableDefinition().variableAliasDefinitionSimple().forEach {
                root.add(OverviewStructureNode(StructureData(it.text + " : " + ctx.dt.text,
                        editor, null, Position.start(it.start))))
            }
            return root
        }

        override fun visitFunction(ctx: TestTableLanguageParser.FunctionContext): OverviewStructureNode {
            val (_, name, _) = ctx.text.split(' ', limit = 3)
            return OverviewStructureNode(StructureData(name, editor, null,
                    Position.start(ctx.start)))
        }

        private fun <E : ParserRuleContext> MutableList<E>.mapAndUnpackTo(root: OverviewStructureNode) {
            mapNotNull { it.accept(this@Visitor) }.forEach {
                it.seq.forEach { c -> root.add(c) }
            }
        }

        private fun <E : ParserRuleContext> MutableList<E>.mapAndAddTo(root: OverviewStructureNode) {
            mapNotNull { it.accept(this@Visitor) }.forEach { root.add(it) }
        }
    }
}

class TTParser(val textArea: CodeEditor, val lookup: Lookup) : AbstractParser() {
    val outlineService by lookup.with<OutlineService>()
    val previewService by lookup.with<GetetaPreviewService>()


    override fun parse(doc: RSyntaxDocument?, style: String?): ParseResult {
        val res = DefaultParseResult(this)
        val parser = GetetaFacade.createParser(CharStreams.fromReader(DocumentReader(doc), textArea.titleText))
        //parser.errorReporter.isPrint = true
        try {
            val ctx = parser.file()
            val gtt = GetetaFacade.parseTableDSL(ctx, )
            parser.errorReporter.throwException()
            val node = TTOverviewTransformer(textArea).create(ctx)
            previewService.render(gtt)
            previewService.select(findCurrentTableByCursor(ctx, textArea.textArea.caretPosition))
            outlineService.show(node)
            lookup.get<ProblemService>().announceProblems(textArea, listOf())
        } catch (e: SyntaxErrorReporter.ParserException) {
            e.errors.forEach {
                res.addNotice(DefaultParserNotice(this, it.msg,
                        it.line, it.offendingSymbol?.startIndex ?: -1,
                        it.offendingSymbol?.text?.length ?: -1))
            }
        } catch (e: NullPointerException) {
        } catch (e: IllegalStateException) {
        }
        return res
    }

    private fun findCurrentTableByCursor(ctx: TestTableLanguageParser.FileContext, caretPosition: Int): String {
        val ctx = ctx.table().find { it: ParserRuleContext -> caretPosition in it.start.startIndex..it.stop.stopIndex }
        return when (val th = ctx?.tableHeader()) {
            is TestTableLanguageParser.TableHeaderFunctionalContext -> th.name.text
            is TestTableLanguageParser.TableHeaderRelationalContext -> th.name.text
            else -> ""
        }
    }
}

class TTFolderParser() : FoldParser {
    override fun getFolds(textArea: RSyntaxTextArea): MutableList<Fold>? {
        val lexer = TestTableLanguageLexer(CharStreams.fromString(textArea.text))
        val folds = arrayListOf<Fold>()
        val stack = Stack<Fold>()
        val stackLine = Stack<Int>()
        var token: Token = lexer.nextToken()
        var inComment = false
        do {
            var type = FoldType.CODE
            var close = false
            var open = false
            if (inComment) {
                if (token.type == TestTableLanguageLexer.COMMENT &&
                        token.text == "*/") {
                    close = true
                    inComment = false
                }
            }
            if (!inComment && token.type == TestTableLanguageLexer.COMMENT && token.text == "/*") {
                open = true; inComment = true; type = FoldType.COMMENT
            }
            if (token.type == TestTableLanguageLexer.RBRACE) close = true
            if (token.type == TestTableLanguageLexer.LBRACE) open = true

            if (close) {
                try {
                    val last = stack.pop()
                    val lastLine = stackLine.pop()
                    last.endOffset = token.stopIndex
                    if (token.line != lastLine)
                        folds += last
                } catch (e: EmptyStackException) {

                }
            }
            if (open) {
                val new = try {
                    val last = stack.peek()
                    last.createChild(type, token.startIndex)
                } catch (e: EmptyStackException) {
                    Fold(type, textArea, token.startIndex)
                }
                stack.push(new)
                stackLine.push(token.line)
            }
            token = lexer.nextToken()
        } while (token.type != Token.EOF)
        return folds
    }

}

