package edu.kit.iti.formal.automation.ide.editors

import edu.kit.iti.formal.automation.ide.*
import edu.kit.iti.formal.automation.ide.tools.*
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.automation.st.ast.Position
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import me.tomassetti.kanvas.AntlrLexerFactory
import me.tomassetti.kanvas.BaseLanguageSupport
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.ParserRuleContext
import org.fife.io.DocumentReader
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice
import org.fife.ui.rsyntaxtextarea.parser.ParseResult
import java.lang.NullPointerException
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
            TestTableLanguageLexer.STATE
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
            //in SEPS -> colors.DARK_GREEN
            //TestTableLanguageLexer.ERROR_CHAR -> RED
            in STRUCTURAL_KEYWORDS -> Colors.structural
            //in CONTROL_KEYWORDS -> colors.control
            in LITERALS -> Colors.literal
            IDENTIFIER -> Colors.identifier
            TestTableLanguageLexer.COMMENT -> Colors.comment
            TestTableLanguageLexer.LINE_COMMENT -> Colors.comment
            else -> Colors.default
        }
    }
}

class TestTableLanguageSupport(lookup: Lookup) : BaseLanguageSupport() {
    override fun createParser(textArea: CodeEditor, lookup: Lookup)
            = TTParser(textArea, lookup)
    override val mimeType: String = "text/gtt"
    override val extension: Collection<String> = setOf("gtt", ".tt.txt", ".tt")
    override val syntaxScheme: SyntaxScheme = TestTableSyntaxScheme(lookup)
    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer =
                    TestTableLanguageLexer(CharStreams.fromString(code))
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

    inner class Visitor : TestTableLanguageBaseVisitor<OverviewStructureNode?>() {
        override fun visitFile(ctx: TestTableLanguageParser.FileContext): OverviewStructureNode {
            val root = OverviewStructureNode(StructureData(editor.titleText.trim('*'), editor, ROOT_ICON))
            ctx.table().mapAndAddTo(root)
            return root
        }

        override fun visitTable(ctx: TestTableLanguageParser.TableContext): OverviewStructureNode? {
            val root = OverviewStructureNode(StructureData(ctx.IDENTIFIER().text, editor, ROOT_ICON))
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
                val n = OverviewStructureNode(StructureData(it.key.text, editor, ROOT_ICON, Position.start(it.key)))
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
            ctx.variableDefinition().forEach {
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
    val problemList by lookup.with<ProblemList>()
    val outlineService by lookup.with<OutlineService>()
    val previewService by lookup.with<GetetaPreviewService>()


    override fun parse(doc: RSyntaxDocument?, style: String?): ParseResult {
        val res = DefaultParseResult(this)
        val parser = GetetaFacade.createParser(CharStreams.fromReader(DocumentReader(doc)))
        //parser.errorReporter.isPrint = true
        try {
            val ctx = parser.file()
            val gtt =  GetetaFacade.parseTableDSL(ctx)
            parser.errorReporter.throwException()
            val node = TTOverviewTransformer(textArea).create(ctx)
            previewService.render(gtt)
            outlineService.show(node)
            problemList.set(textArea, listOf())
        } catch (e: SyntaxErrorReporter.ParserException) {
            e.errors.forEach {
                res.addNotice(DefaultParserNotice(this, it.msg,
                        it.line, it.offendingSymbol?.startIndex ?: -1,
                        it.offendingSymbol?.text?.length ?: -1))
            }
        } catch (e : NullPointerException) {

        }
        return res
    }
}
