package edu.kit.iti.formal.automation.fx

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Lexer.*
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.smt.SmtLibv2Lexer
import edu.kit.iti.formal.smv.parser.SMVLexer
import javafx.beans.binding.Bindings
import javafx.beans.property.SimpleBooleanProperty
import javafx.beans.property.SimpleObjectProperty
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.fxmisc.richtext.CodeArea
import org.fxmisc.richtext.LineNumberFactory
import org.fxmisc.richtext.model.StyleSpans
import org.fxmisc.richtext.model.StyleSpansBuilder
import java.io.File
import java.util.*

object Editors {
    fun getLanguageForFilename(file: File) = getEditorForSuffix(file.extension)
    fun getEditorForSuffix(suffix: String): Language? =
        when (suffix) {
            ".tt", ".gtt" -> TTLanguage
            "st", "iec" -> StLanguage
            "smv" -> SmvLanguage
            "smt" -> SmtLanguage
            else -> null
        }
}


open class Editor : Controller {
    override val ui = CodeArea("")
    val dirty = SimpleBooleanProperty(this, "dirty", false)
    val filename = SimpleObjectProperty<File>(this, "filename", null)
    val language = SimpleObjectProperty<Language>(this, "language", null)

    val title = Bindings.createStringBinding(
        { -> (filename.value?.name ?: "unknown") + (if (dirty.value) "*" else "") },
        dirty,
        filename
    )

    init {
        ui.paragraphGraphicFactory = LineNumberFactory.get(ui) //{ String.format("%03d", it) }
        ui.isLineHighlighterOn = true
        ui.textProperty().addListener { _, _, newText: String ->
            language.value?.also {
                ui.setStyleSpans(0, computeHighlighting(it))
            }
        }
        filename.addListener { _, _, new ->
            language.value = Editors.getLanguageForFilename(new)
        }

        language.addListener { _, _, new ->
            new?.also {
                if(ui.text.isNotEmpty())
                    ui.setStyleSpans(0, computeHighlighting(it))
            }
        }
    }


    fun computeHighlighting(language: Language): StyleSpans<Collection<String>>? {
        val text = ui.text
        val spansBuilder = StyleSpansBuilder<Collection<String>>()
        val lexer = language.lexerFactory(CharStreams.fromString(text))
        do {
            val tok = lexer.nextToken()
            if (tok.type == -1) break
            val typ = language.getStyleClass(tok.type)// lexer.vocabulary.getSymbolicName(tok.type)
            spansBuilder.add(Collections.singleton(typ), tok.text.length);
        } while (tok.type != -1)
        return spansBuilder.create()
    }
}

abstract class Language {
    abstract val name: String
    abstract fun lexerFactory(input: CharStream): Lexer

    protected var structural: Set<Int> = setOf()
    protected var separators: Set<Int> = setOf()
    protected var literals: Set<Int> = setOf()
    protected var identifiers: Set<Int> = setOf()
    protected var specialIds: Set<Int> = setOf()
    protected var comments: Set<Int> = setOf()
    protected var datatype: Set<Int> = setOf()
    protected var control: Set<Int> = setOf()
    protected var operators: Set<Int> = setOf()
    protected var errorChar: Int = -2

    fun getStyleClass(tokenType: Int) =
        when (tokenType) {
            in separators -> "separator"
            in structural -> "structural"
            in literals -> "literal"
            in identifiers -> "identifier"
            in specialIds -> "fancy-identifier"
            in comments -> "comment"
            in datatype -> "datatype"
            in control -> "control"
            in operators -> "operators"
            else -> {
                System.err.println("token type $tokenType (${javaClass.name}) is not registered for syntax highlightning.")
                ""
            }
        }
}

object StLanguage : Language() {
    override val name: String = "StructuredText"

    override fun lexerFactory(input: CharStream): Lexer = IEC61131Lexer(input)

    private fun MutableSet<Int>.addAll(vararg items: Int) {
        items.forEach { add(it) }
    }

    init {
        structural = setOf(
            PROGRAM, INITIAL_STEP, TRANSITION,
            END_TRANSITION, END_VAR, VAR,
            VAR_ACCESS, VAR_CONFIG, VAR_EXTERNAL,
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
            ACTION, END_ACTION
        )

        setOf(
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
            BOOL
        )

        literals = setOf(
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

        control = setOf(
            IF, ELSE, ELSEIF, FOR, END_FOR,
            WHILE, END_WHILE, REPEAT, END_REPEAT,
            END_IF, DO, THEN, UNTIL, TO,
            WITH, CASE, END_CASE, OF
        )

        operators = setOf(
            NOT, AND, OR, MOD, DIV, MULT, MINUS, EQUALS, NOT_EQUALS,
            GREATER_EQUALS, GREATER_THAN, LESS_EQUALS, LESS_THAN,
            IL_ADD, IL_ANDN, IL_CAL, IL_CALC, IL_CALCN, IL_CD, IL_CLK,
            IL_CU, IL_DIV, IL_EQ, IL_GE, IL_GT, IL_IN, IL_JMP, IL_JMPC, IL_JMPCN, IL_LD, IL_LDN, IL_LE, IL_LT,
            IL_MOD, IL_MUL, IL_NE, IL_NOT, IL_ORN, IL_PT, IL_PV, IL_R1, IL_R, IL_RET, IL_RETC, IL_RETCN,
            IL_S1, IL_S, IL_ST, IL_STN, IL_STQ, IL_SUB, IL_XORN, IL_OR
        )

        identifiers = setOf(IDENTIFIER)
        comments = setOf(LINE_COMMENT, COMMENT)
        errorChar = ERROR_CHAR
    }
}

object TTLanguage : Language() {
    override val name: String = "TestTables"

    override fun lexerFactory(input: CharStream): Lexer = TestTableLanguageLexer(input)

    init {
        structural = setOf(
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
        separators = setOf(
            TestTableLanguageLexer.RBRACE,
            TestTableLanguageLexer.LBRACE,
            TestTableLanguageLexer.RPAREN,
            TestTableLanguageLexer.LPAREN,
            TestTableLanguageLexer.RBRACKET,
            TestTableLanguageLexer.LBRACKET,
            TestTableLanguageLexer.COLON,
            TestTableLanguageLexer.COMMA
        )
        literals = setOf(
            TestTableLanguageLexer.INTEGER
        )
        identifiers = setOf(TestTableLanguageLexer.FQ_VARIABLE, TestTableLanguageLexer.IDENTIFIER)
        comments = setOf(TestTableLanguageLexer.COMMENT, TestTableLanguageLexer.LINE_COMMENT)
    }
}

object SmvLanguage : Language() {
    override val name: String = "Symbolic Model Verifier"

    override fun lexerFactory(input: CharStream): Lexer = SMVLexer(input)
}

object SmtLanguage : Language() {
    override val name: String = "SMT"
    override fun lexerFactory(input: CharStream): Lexer = SmtLibv2Lexer(input)
}

enum class StyleNames {

}