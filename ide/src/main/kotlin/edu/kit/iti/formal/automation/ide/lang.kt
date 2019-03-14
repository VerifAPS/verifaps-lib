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

class IECLanguageSupport(lookup: Lookup) : BaseLanguageSupport<Node>() {

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
        style.foreground = when (index) {
            in STRUCTURAL_KEYWORDS -> colors.DARK_VIOLET
            in LITERALS -> colors.VIOLET
            in SEPS -> colors.DARK_GREEN
            TestTableLanguageLexer.IDENTIFIER -> colors.BLUE
            TestTableLanguageLexer.COMMENT -> colors.GREY
            TestTableLanguageLexer.LINE_COMMENT -> colors.GREY
            //TestTableLanguageLexer.ERROR_CHAR -> RED
            else -> Color.BLACK
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

class IEC61131SyntaxScheme(lookup: Lookup) : SyntaxScheme(true) {
    val colors: Colors by lookup.with()
    val STRUCTURAL_KEYWORDS = setOf(
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
            IEC61131Lexer.FUNCTION,
            IEC61131Lexer.END_FUNCTION,
            IEC61131Lexer.END_INTERFACE,
            IEC61131Lexer.END_METHOD,
            IEC61131Lexer.INTERFACE,
            IEC61131Lexer.METHOD,
            IEC61131Lexer.END_NAMESPACE,
            IEC61131Lexer.NAMESPACE,
            IEC61131Lexer.END_STEP,
            IEC61131Lexer.STEP,
            IEC61131Lexer.ACTION
    )
    val DATATYPE_KEYWORD = setOf(
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
            IEC61131Lexer.BOOL
    )
    val LITERALS = setOf(
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


    override fun getStyle(index: Int): Style {
        val style = Style()
        val color = when (index) {
            in STRUCTURAL_KEYWORDS -> colors.DARK_VIOLET
            in LITERALS -> colors.VIOLET
            in DATATYPE_KEYWORD -> colors.DARK_GREEN
            IEC61131Lexer.IDENTIFIER -> colors.BLUE
            IEC61131Lexer.COMMENT -> colors.GREY
            IEC61131Lexer.LINE_COMMENT -> colors.GREY
            IEC61131Lexer.ERROR_CHAR -> Color.RED
            else -> Color.BLACK
        }
        if (color != null) {
            style.foreground = color
        }
        return style
    }
}
