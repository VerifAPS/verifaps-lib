package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Lexer.*
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
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import org.fife.ui.rsyntaxtextarea.folding.Fold
import org.fife.ui.rsyntaxtextarea.folding.FoldParser
import org.fife.ui.rsyntaxtextarea.folding.FoldType
import java.awt.Font
import java.io.InputStream
import java.util.*
import javax.swing.text.BadLocationException

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
            in STRUCTURAL_KEYWORDS -> colors.structural
            //in CONTROL_KEYWORDS -> colors.control
            in LITERALS -> colors.literal
            IDENTIFIER -> colors.identifier
            TestTableLanguageLexer.COMMENT -> colors.comment
            TestTableLanguageLexer.LINE_COMMENT -> colors.comment
            else -> colors.default
        }
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
            FUNCTION,
            END_FUNCTION,
            END_INTERFACE,
            END_METHOD,
            INTERFACE,
            METHOD,
            END_NAMESPACE,
            NAMESPACE,
            END_STEP,
            STEP,
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
            IF, ELSE, ELSEIF, FOR, END_FOR, WHILE, END_WHILE, REPEAT, END_REPEAT,
            DO, THEN, UNTIL, TO, WITH, CASE, END_CASE, OF
    )

    override fun getStyle(index: Int): Style {
        return when (index) {
            in STRUCTURAL_KEYWORDS -> colors.structural
            in CONTROL_KEYWORDS -> colors.control
            in LITERALS -> colors.literal
            in DATATYPE_KEYWORD -> colors.types
            IDENTIFIER -> colors.identifier
            COMMENT -> colors.comment
            LINE_COMMENT -> colors.comment
            ERROR_CHAR -> colors.error
            else -> colors.default
        }
    }
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
