package edu.kit.iti.formal.automation.ide.editors

import edu.kit.iti.formal.automation.ide.AntlrLexerFactory
import edu.kit.iti.formal.automation.ide.CodeEditor
import edu.kit.iti.formal.automation.ide.Colors
import edu.kit.iti.formal.automation.ide.Lookup
import edu.kit.iti.formal.smv.parser.SMVLexer
import edu.kit.iti.formal.smv.parser.SMVLexer.*
import me.tomassetti.kanvas.BaseLanguageSupport
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import java.util.*

class SmvLanguageSupport(lookup: Lookup) : BaseLanguageSupport() {
    override val mimeType: String = "text/smv"
    override val extension: Collection<String> = Collections.singleton("smv")
    override val syntaxScheme: SyntaxScheme = SmvSyntaxScheme(lookup)
    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer =
                    SMVLexer(CharStreams.fromString(code))
        }
    //override val parserData: ParserData?
    //    get() = ParserData(SMVParser.ruleNames, SMVLexer.VOCABULARY, SMVLexer._ATN)
}

class SmvSyntaxScheme(lookup: Lookup) : SyntaxScheme(true) {
    private val colors: Colors by lookup.with()

    private val STRUCTURAL_KEYWORDS = setOf(
            ASSIGN, TRANS, CTLSPEC, SPEC, PSLSPEC, LTLSPEC, INVAR, INVARSPEC, MODULE,
            INIT, NEXT, ARRAY, ASSIGN, BOOLEAN, CASE, COMMA, COMPASSION, CONSTANTS,
            CTLSPEC, DEFINE, FAIRNESS, FROZENVAR, INITBIG, INVAR,
            INVARSPEC, ISA, IVAR, JUSTICE, LTLSPEC, MODULE, NAME, PROCESS,
            PSLSPEC, SIGNED, SPEC,
            TRANS, UNSIGNED,
            VAR, WORD, OF
    )
    private val SEPS = setOf(
            COLON, COLONEQ, DCOLON, SEMI, LBRACE, RBRACE, LPAREN, RPAREN, RBRACKET, LBRACKET, DOTDOT, DOT)

    private val OPERATORS = setOf(S,
            IN, INIT, NEXT, LT, LTE, MINUS, MOD, NEQ, O, OR,
            PLUS, SHIFTL, SHIFTR, STAR, DIV, EF, EG, EQ, EQUIV, ESAC,
            EU, EX, F, G, GT, GTE, H, IMP, V, X, XNOR, XOR, Y, Z, NOT,
            AF, AG, AND, AU, AX, T, U, UNION
    )

    private val LITERALS = setOf(
            TRUE, FALSE, WORD_LITERAL, FLOAT, NUMBER
    )

    override fun getStyle(index: Int): Style {
        return when (index) {
            in SEPS -> colors.separators
            ERROR_CHAR -> colors.error
            in STRUCTURAL_KEYWORDS -> colors.structural
            in OPERATORS -> colors.control
            in LITERALS -> colors.literal
            ID -> colors.identifier
            SL_COMMENT -> colors.comment
            else -> colors.default
        }
    }
}
