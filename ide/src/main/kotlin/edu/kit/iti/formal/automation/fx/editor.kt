/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 *
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.fx

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.analysis.ReportCategory
import edu.kit.iti.formal.automation.analysis.ReportLevel
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Lexer.*
import edu.kit.iti.formal.automation.st.ast.Position
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.smt.SmtLibv2Lexer
import edu.kit.iti.formal.smv.parser.SMVLexer
import javafx.beans.InvalidationListener
import javafx.beans.binding.Bindings
import javafx.beans.property.SimpleBooleanProperty
import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.collections.FXCollections
import javafx.stage.Popup
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token
import org.fxmisc.richtext.CodeArea
import org.fxmisc.richtext.LineNumberFactory
import org.fxmisc.richtext.event.MouseOverTextEvent
import org.fxmisc.richtext.model.StyleSpans
import org.fxmisc.richtext.model.StyleSpansBuilder
import org.reactfx.EventStreams
import tornadofx.*
import tornadofx.EventBus.RunOn.ApplicationThread
import java.io.File
import java.time.Duration
import java.util.*

object NewIssues : FXEvent(ApplicationThread)

object Editors {
    fun getLanguageForFilename(file: File) = getEditorForSuffix(file.extension)
    fun getEditorForSuffix(suffix: String): Language? = when (suffix) {
        "tt", "gtt" -> TTLanguage
        "st", "iec" -> StLanguage
        "smv" -> SmvLanguage
        "smt" -> SmtLanguage
        else -> null
    }
}

open class Editor : View() {
    final override val root = CodeArea("")
    val dirtyProperty = SimpleBooleanProperty(this, "dirty", false)
    val dirty by dirtyProperty
    val filenameProperty = SimpleObjectProperty<File>(this, "filename", null)
    val filename by filenameProperty
    val languageProperty = SimpleObjectProperty<Language>(this, "language", null)
    val language by languageProperty
    val issuesProperty = SimpleListProperty<Problem>(this, "issues", FXCollections.observableArrayList())
    val issues by issuesProperty

    val editorTitle = Bindings.createStringBinding(
        { (filenameProperty.value?.name ?: "unknown") + (if (dirtyProperty.value) "*" else "") },
        dirtyProperty,
        filenameProperty,
    )

    init {
        root.paragraphGraphicFactory = LineNumberFactory.get(root)
        root.isLineHighlighterOn = true

        EventStreams.changesOf(root.textProperty())
            .subscribe {
                languageProperty.value?.also {
                    reHighlight()
                }
            }

        EventStreams.changesOf(root.textProperty())
            .forgetful()
            .successionEnds(Duration.ofMillis(500))
            .subscribe { runLinter() }

        issuesProperty.addListener(InvalidationListener { _ -> reHighlight() })

        filenameProperty.addListener { _, _, new ->
            languageProperty.value = Editors.getLanguageForFilename(new)
        }

        languageProperty.addListener { _, _, new ->
            new?.also {
                if (root.text.isNotEmpty()) {
                    reHighlight()
                }
            }
        }

        root.mouseOverTextDelay = Duration.ofMillis(200)
        val popup = Popup()
        root.addEventHandler(MouseOverTextEvent.MOUSE_OVER_TEXT_BEGIN) { e ->
            val chIdx = e.characterIndex
            issues.find { it.startOffset <= chIdx && chIdx <= it.endOffset }?.let { issue ->
                val popupMsg = label(issue.message) {
                    style {
                        backgroundColor += c("black")
                        fill = c("white")
                        paddingAll = 5
                    }
                }
                popup.content.add(popupMsg)
                val pos = e.screenPosition
                popup.show(currentWindow, pos.x, pos.y + 10)
            }
        }
        root.addEventHandler(MouseOverTextEvent.MOUSE_OVER_TEXT_END) { e -> popup.hide() }
    }

    private fun runLinter() {
        val text = root.text
        language?.parseFile(CharStreams.fromString(text))?.let {
            issues.setAll(it)
        }
    }

    private fun reHighlight() {
        language?.let {
            try {
                root.setStyleSpans(0, computeHighlighting(it))
            } catch (e: Exception) {
                /*ignore*/
            }

            try {
                issues.forEach {
                    root.setStyle(
                        it.startOffset,
                        it.endOffset + 1,
                        Collections.singleton("error"),
                    )
                }
            } catch (e: Exception) {
                /*ignore*/
            }
        }
    }

    fun computeHighlighting(language: Language): StyleSpans<Collection<String>>? {
        val text = root.text
        val spansBuilder = StyleSpansBuilder<Collection<String>>()
        val lexer = language.lexerFactory(CharStreams.fromString(text))
        do {
            val tok = lexer.nextToken()
            if (tok.type == -1) break
            val typ = language.getStyleClass(tok.type) // lexer.vocabulary.getSymbolicName(tok.type)
            spansBuilder.add(Collections.singleton(typ), tok.text.length)
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

    fun getStyleClass(tokenType: Int) = when (tokenType) {
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

    abstract fun parseFile(fromString: CharStream): List<Problem>?
}

object StLanguage : Language() {
    override val name: String = "StructuredText"

    override fun lexerFactory(input: CharStream): Lexer = IEC61131Lexer(input)
    override fun parseFile(fromString: CharStream): List<Problem> {
        val (_, errors) = IEC61131Facade.fileResolve(fromString, true)
        return errors
    }

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
            TYPE,
            END_TYPE,
            STRUCT, END_STRUCT,
            CONFIGURATION, END_CONFIGURATION,
            ACTION, END_ACTION,
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
            BOOL,
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
            WSTRING_LITERAL,
        )

        control = setOf(
            IF, ELSE, ELSEIF, FOR, END_FOR,
            WHILE, END_WHILE, REPEAT, END_REPEAT,
            END_IF, DO, THEN, UNTIL, TO,
            WITH, CASE, END_CASE, OF,
        )

        operators = setOf(
            NOT, AND, OR, MOD, DIV, MULT, MINUS, EQUALS, NOT_EQUALS,
            GREATER_EQUALS, GREATER_THAN, LESS_EQUALS, LESS_THAN,
            IL_ADD, IL_ANDN, IL_CAL, IL_CALC, IL_CALCN, IL_CD, IL_CLK,
            IL_CU, IL_DIV, IL_EQ, IL_GE, IL_GT, IL_IN, IL_JMP, IL_JMPC, IL_JMPCN, IL_LD, IL_LDN, IL_LE, IL_LT,
            IL_MOD, IL_MUL, IL_NE, IL_NOT, IL_ORN, IL_PT, IL_PV, IL_R1, IL_R, IL_RET, IL_RETC, IL_RETCN,
            IL_S1, IL_S, IL_ST, IL_STN, IL_STQ, IL_SUB, IL_XORN, IL_OR,
        )

        identifiers = setOf(IDENTIFIER)
        comments = setOf(LINE_COMMENT, COMMENT)
        errorChar = ERROR_CHAR
    }
}

object TTLanguage : Language() {
    override val name: String = "TestTables"

    override fun lexerFactory(input: CharStream): Lexer = TestTableLanguageLexer(input)
    override fun parseFile(fromString: CharStream): List<Problem> {
        val p = GetetaFacade.createParser(fromString)
        p.file()
        return p.errorReporter.errors.map {
            val tok = it.offendingSymbol as Token
            Problem(
                tok.tokenSource.sourceName ?: "",
                it.msg ?: "syntax error",
                Position.start(tok),
                Position.end(tok),
                ReportCategory.SYNTAX,
                ReportLevel.ERROR,
            )
        }
    }

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
            TestTableLanguageLexer.RELATIONAL,
        )
        separators = setOf(
            TestTableLanguageLexer.RBRACE,
            TestTableLanguageLexer.LBRACE,
            TestTableLanguageLexer.RPAREN,
            TestTableLanguageLexer.LPAREN,
            TestTableLanguageLexer.RBRACKET,
            TestTableLanguageLexer.LBRACKET,
            TestTableLanguageLexer.COLON,
            TestTableLanguageLexer.COMMA,
        )
        literals = setOf(
            TestTableLanguageLexer.INTEGER,
        )
        identifiers = setOf(TestTableLanguageLexer.FQ_VARIABLE, TestTableLanguageLexer.IDENTIFIER)
        comments = setOf(TestTableLanguageLexer.COMMENT, TestTableLanguageLexer.LINE_COMMENT)
    }
}

object SmvLanguage : Language() {
    override val name: String = "Symbolic Model Verifier"

    override fun lexerFactory(input: CharStream): Lexer = SMVLexer(input)
    override fun parseFile(fromString: CharStream): List<Problem>? = null
}

object SmtLanguage : Language() {
    override val name: String = "SMT"
    override fun lexerFactory(input: CharStream): Lexer = SmtLibv2Lexer(input)
    override fun parseFile(fromString: CharStream): List<Problem>? = null
}
