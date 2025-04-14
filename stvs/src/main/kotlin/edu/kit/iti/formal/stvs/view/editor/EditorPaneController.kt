package edu.kit.iti.formal.stvs.view.editor

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.code.ParsedCode.Companion.parseCode
import edu.kit.iti.formal.stvs.model.code.SyntaxError
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.view.Controller
import javafx.application.Platform
import javafx.concurrent.Task
import javafx.event.Event
import javafx.event.EventHandler
import javafx.scene.control.ContextMenu
import javafx.scene.control.MenuItem
import javafx.scene.control.SeparatorMenuItem
import javafx.scene.input.KeyEvent
import org.antlr.v4.runtime.Token
import org.fxmisc.richtext.model.StyleSpans
import org.fxmisc.richtext.model.StyleSpansBuilder
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon
import java.time.Duration
import java.util.*
import java.util.concurrent.Executors

/**
 * Created by csicar on 09.01.17. Some parts are inspired by examples of the used library:
 * https://github.com/TomasMikula/RichTextFX/blob/a098da6309a0f624052fd1d4d6f5079dd6265fbe/richtextfx-demos/src/main/java/org/fxmisc/richtext/demo/JavaKeywords.java
 *
 * @author Lukas Fritsch
 */
class EditorPaneController(val code: Code, private val globalConfig: GlobalConfig) : Controller {
    override val view: EditorPane = EditorPane(
        code.sourcecode,
        code.syntaxErrorsProperty
    )
    private val executor = Executors.newSingleThreadExecutor()

    /**
     *
     * Creates the controller for the [EditorPane].
     *
     * @param code         the code file to be shown
     * @param globalConfig the global configuration (for font size or style)
     */
    init {
        view.stylesheets
            .add(
                EditorPane::class.java.getResource("st-keywords.css")
                    .toExternalForm()
            )
        configureTextArea()
        setupContextMenu()
        handleTextChange(computeHighlighting(code.sourcecode))
        globalConfig.editorFontSizeProperty.addListener { _, _, newValue -> updateFontSize(newValue.toInt()) }
        globalConfig.editorFontFamilyProperty.addListener { _, _, newValue -> updateFontFamily(newValue) }
        updateFontFamily(globalConfig.editorFontFamily)
        updateFontSize(globalConfig.editorFontSize)
        filterAltEvents()
    }

    private fun filterAltEvents() {
        val handler = EventHandler { e: KeyEvent ->
            if (e.isAltDown) {
                Event.fireEvent(this.view, e)
            }
        }
        view.codeArea.onKeyPressed = handler
    }

    private fun updateFontFamily(fontFamily: String) {
        view.codeArea.style = ("-fx-font-family: " + fontFamily + ";" + "-fx-font-size: "
                + globalConfig.editorFontSizeProperty.get() + "pt;")
    }

    private fun updateFontSize(size: Int) {
        view.codeArea.style = "-fx-font-family: " + globalConfig.editorFontFamilyProperty
            .get() + ";" + "-fx-font-size: " + size + "pt;"
    }

    private fun createMenuItem(
        name: String, action: Runnable,
        icon: FontAwesomeSolid
    ): MenuItem {
        val item = createMenuItem(name, action)
        item.graphic = FontIcon(icon)
        return item
    }

    private fun createMenuItem(name: String, action: Runnable): MenuItem {
        val item = MenuItem(name)
        item.onAction = EventHandler { action.run() }
        return item
    }


    private fun setupContextMenu() {
        val codeArea = view.codeArea

        val menu = ContextMenu()
        menu.items.addAll(
            createMenuItem(
                "Undo", { codeArea.undo() },
                FontAwesomeSolid.UNDO
            ), createMenuItem("Redo") { codeArea.redo() },
            SeparatorMenuItem(),
            createMenuItem("Paste", { codeArea.paste() }, FontAwesomeSolid.PASTE),
            createMenuItem("Copy", { codeArea.copy() }, FontAwesomeSolid.COPY),
            createMenuItem("Cut", { codeArea.cut() }, FontAwesomeSolid.CUT),
            createMenuItem("Select All") { codeArea.selectAll() })
        view.contextMenu = menu
    }

    private fun configureTextArea() {
        val codeArea = view.codeArea
        code.sourceCodeProperty.bind(codeArea.textProperty())
        codeArea.richChanges()
            .filter { ch -> ch.inserted != ch.removed }
            .successionEnds(Duration.ofMillis(500))
            .hook { _ -> codeArea.undoManager.mark() }
            .supplyTask { this.computeHighlightingAsync() }
            .awaitLatest(codeArea.richChanges())
            .filterMap {
                if (it.isSuccess) {
                    Optional.of(it.get())
                } else {
                    it.failure.printStackTrace()
                    Optional.empty()
                }
            }
            .subscribe { this.handleTextChange(it) }
    }

    private fun computeHighlightingAsync(): Task<StyleSpans<Collection<String>>> {
        val codeArea = view.codeArea
        val sourcecode = codeArea.text
        val task = object : Task<StyleSpans<Collection<String>>>() {
            @Throws(Exception::class)
            override fun call(): StyleSpans<Collection<String>> {
                return computeHighlighting(sourcecode)
            }
        }
        executor.execute(task)
        return task
    }

    private fun computeHighlighting(
        sourcecode: String
    ): StyleSpans<Collection<String>> {
        val spansBuilder = StyleSpansBuilder<Collection<String>>()

        if (sourcecode.isEmpty()) {
            spansBuilder.add(emptyList(), 0)
            return spansBuilder.create()
        }

        val tokens: MutableList<Token> = ArrayList()
        val syntaxErrors: MutableList<SyntaxError> = ArrayList()

        // Short-circuit setting parsed code properties on code, since we're in another thread.
        parseCode(
            sourcecode,
            {
                tokens.addAll(it)
                Platform.runLater { code.tokensProperty.setAll(it) }
            }, {
                syntaxErrors.addAll(it)
                Platform.runLater { code.syntaxErrorsProperty.setAll(it) }
            }, { Platform.runLater { code.parsedCodeProperty.set(it) } })


        if (tokens.isEmpty()) {
            spansBuilder.add(emptyList(), 0)
            return spansBuilder.create()
        }

        tokens.forEach { token: Token ->
            // replaceAll is a work-around for a bug when ANTLR has a
            // different character count than this CodeArea.
            spansBuilder.add(
                getStyleClassesFor(token, syntaxErrors),
                token.text.replace("\\r".toRegex(), "").length
            )
        }
        return spansBuilder.create()
    }

    private fun getStyleClassesFor(token: Token, syntaxErrors: List<SyntaxError>): Collection<String> {
        val error = syntaxErrors.any { it.isToken(token) }
        return if (error) {
            listOf("syntax-error")
        } else {
            getHightlightingClass(token)
        }
    }

    private fun getHightlightingClass(token: Token?): List<String> {
        return when (token!!.type) {
            IEC61131Lexer.COMMENT, IEC61131Lexer.LINE_COMMENT -> listOf("comment")
            IEC61131Lexer.RETURN, IEC61131Lexer.INTERFACE, IEC61131Lexer.END_INTERFACE, IEC61131Lexer.METHOD,
            IEC61131Lexer.END_METHOD, IEC61131Lexer.EXTENDS, IEC61131Lexer.IMPLEMENTS, IEC61131Lexer.ELSEIF,
            IEC61131Lexer.THEN, IEC61131Lexer.OF, IEC61131Lexer.PROGRAM, IEC61131Lexer.END_PROGRAM, IEC61131Lexer.TYPE,
            IEC61131Lexer.END_TYPE, IEC61131Lexer.IF, IEC61131Lexer.END_IF, IEC61131Lexer.FUNCTION,
            IEC61131Lexer.END_FUNCTION, IEC61131Lexer.FUNCTION_BLOCK, IEC61131Lexer.END_FUNCTION_BLOCK,
            IEC61131Lexer.CASE, IEC61131Lexer.END_CASE, IEC61131Lexer.ELSE -> listOf("keyword")

            IEC61131Lexer.INT, IEC61131Lexer.SINT, IEC61131Lexer.DINT, IEC61131Lexer.LINT, IEC61131Lexer.UINT,
            IEC61131Lexer.ULINT, IEC61131Lexer.USINT, IEC61131Lexer.UDINT, IEC61131Lexer.BOOL, IEC61131Lexer.BYTE,
            IEC61131Lexer.WORD, IEC61131Lexer.LWORD, IEC61131Lexer.DWORD -> listOf("type")

            IEC61131Lexer.INTEGER_LITERAL -> listOf("number")

            IEC61131Lexer.STRING_LITERAL, IEC61131Lexer.REAL_LITERAL, IEC61131Lexer.RETAIN, IEC61131Lexer.F_EDGE,
            IEC61131Lexer.R_EDGE, IEC61131Lexer.VAR_ACCESS, IEC61131Lexer.VAR_TEMP, IEC61131Lexer.VAR_EXTERNAL,
            IEC61131Lexer.VAR_CONFIG, IEC61131Lexer.REAL, IEC61131Lexer.LREAL -> listOf("unsupported")

            IEC61131Lexer.VAR, IEC61131Lexer.VAR_INPUT, IEC61131Lexer.VAR_IN_OUT, IEC61131Lexer.VAR_OUTPUT,
            IEC61131Lexer.CONSTANT, IEC61131Lexer.END_VAR -> listOf("vardef")

            IEC61131Lexer.AND, IEC61131Lexer.NOT, IEC61131Lexer.OR, IEC61131Lexer.MOD -> listOf("operation")
            else -> listOf()
        }
    }

    private fun handleTextChange(highlighting: StyleSpans<Collection<String>>) {
        view.setStyleSpans(highlighting)
    }
}
