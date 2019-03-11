package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import me.tomassetti.kanvas.AntlrLexerFactory
import me.tomassetti.kanvas.BaseLanguageSupport
import me.tomassetti.kanvas.ParserData
import me.tomassetti.kolasu.model.Node
import me.tomassetti.kolasu.parsing.ParsingResult
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import java.awt.Color
import java.io.InputStream

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.03.19)
 */
class IecChecker : me.tomassetti.kolasu.parsing.Parser<Node> {
    override fun parse(inputStream: InputStream, withValidation: Boolean): ParsingResult<Node> {
        /*val elements = IEC61131Facade.file(inputStream)
        IEC61131Facade.resolveDataTypes(elements)
        val issues = IEC61131Facade.check(elements)
                    */
        TODO()
    }
}


class IECLanguageSupport(lookup: Lookup) :
        BaseLanguageSupport<Node>() {

    override val parser: me.tomassetti.kolasu.parsing.Parser<Node> = IecChecker()
    override val syntaxScheme: SyntaxScheme = IEC61131SyntaxScheme(lookup)
    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer =
                    IEC61131Lexer(CharStreams.fromString(code))
        }
    override val parserData: ParserData?
        get() = ParserData(IEC61131Parser.ruleNames, IEC61131Parser.VOCABULARY, IEC61131Parser._ATN)
}


class TestTableSyntaxScheme(lookup: Lookup) : SyntaxScheme(true) {
    private val colors: Colors by lookup.with()
    private val STRUCTURAL_KEYWORDS = setOf(
            TestTableLanguageLexer.OPTIONS,
            TestTableLanguageLexer.TABLE,
            TestTableLanguageLexer.FUNCTION,
            TestTableLanguageLexer.OF,
            TestTableLanguageLexer.WITH,
            TestTableLanguageLexer.AS,
            TestTableLanguageLexer.IF,
            TestTableLanguageLexer.FI
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
        val style = Style()
        val color = when (index) {
            in STRUCTURAL_KEYWORDS -> colors.DARK_VIOLET
            in LITERALS -> colors.VIOLET
            in SEPS -> colors.DARK_GREEN
            TestTableLanguageLexer.IDENTIFIER -> colors.BLUE
            TestTableLanguageLexer.COMMENT -> colors.GREY
            TestTableLanguageLexer.LINE_COMMENT -> colors.GREY
            //TestTableLanguageLexer.ERROR_CHAR -> RED
            else -> Color.BLACK
        }
        if (color != null) {
            style.foreground = color
        }
        return style
    }
}

class TestTableLanguageSupport(lookup: Lookup) : BaseLanguageSupport<Node>() {
    override val parser: me.tomassetti.kolasu.parsing.Parser<Node>
        get() = TODO()
    override val syntaxScheme: SyntaxScheme = TestTableSyntaxScheme(lookup)
    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer =
                    TestTableLanguageLexer(CharStreams.fromString(code))
        }
    override val parserData: ParserData?
        get() = ParserData(TestTableLanguageParser.ruleNames,
                TestTableLanguageLexer.VOCABULARY, TestTableLanguageLexer._ATN)
}

