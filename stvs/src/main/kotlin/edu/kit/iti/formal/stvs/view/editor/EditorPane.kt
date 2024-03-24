package edu.kit.iti.formal.stvs.view.editor

import de.jensd.fx.glyphs.GlyphsDude
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon
import edu.kit.iti.formal.stvs.model.code.*
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.layout.HBox
import org.fxmisc.richtext.CodeArea
import org.fxmisc.richtext.LineNumberFactory
import org.fxmisc.richtext.model.StyleSpans
import java.util.function.IntFunction

/**
 *
 *
 * The view for the left side of our application: The code editor.
 *
 *
 *
 *
 * This view contains both the [CodeArea] for editing the code and the [ListView] for
 * viewing a list of syntax errors. It itself extends a [SplitPane] for combining these two
 * views.
 *
 *
 *
 *
 * Created by csicar on 09.01.17.
 *
 *
 * @author Lukas Fritsch
 */
class EditorPane @JvmOverloads constructor(
    code: String?, private val syntaxErrors: ObservableList<SyntaxError?>,
    showLineNumbers: Boolean = true
) : SplitPane() {
    var codeArea: CodeArea
        private set

    private val lineNumberFactory: IntFunction<Node>

    /**
     * Creates an editable EditorPane with the given code as initial source code text.
     * @param code the string to initialize the [CodeArea] to
     * @param syntaxErrors the initial list of [SyntaxError]s.
     * @param showLineNumbers whether to show line numbers in the [CodeArea]
     */
    /**
     *
     *
     * Creates an EditorPane with the given code as initial source code text.
     *
     *
     *
     *
     * This is a default constructor (see [.EditorPane]) for
     * initializing showing of lines to true
     *
     *
     * @param code the string to initialize the [CodeArea] to
     * @param syntaxErrors the initial list of [SyntaxError]s.
     */
    init {
        ViewUtils.setupView(this)

        codeArea = CodeArea(code)
        lineNumberFactory = LineNumberFactory.get(codeArea)
        if (showLineNumbers) {
            codeArea.paragraphGraphicFactory = IntFunction { i: Int -> this.createLinePrefixForLine(i) }
        }
        items.addAll(codeArea)
        this.orientation = Orientation.VERTICAL
        this.setDividerPositions(0.8)
    }

    private fun setLineIcon(i: Int, syntaxErrors: List<SyntaxError>, icon: Label) {
        icon.isVisible = syntaxErrors.isNotEmpty()
        val combinedMessages: String = syntaxErrors.joinToString("\n") { it.message }
        icon.tooltip = Tooltip(combinedMessages)
    }

    /**
     * prefix the line with the line number and possibly an error icon
     * @param i line number
     * @return Node intended as the prefix
     */
    private fun createLinePrefixForLine(i: Int): Node {
        val icon = GlyphsDude.createIconLabel(FontAwesomeIcon.EXCLAMATION_CIRCLE, "", null, null, null)
        val lineSyntaxErrors = syntaxErrors.filtered { syntaxError -> syntaxError!!.line == i + 1 }
            .filterNotNull()
        setLineIcon(i, lineSyntaxErrors, icon)
        syntaxErrors.addListener { change: ListChangeListener.Change<*>? ->
            setLineIcon(i, lineSyntaxErrors, icon)
        }
        return HBox(lineNumberFactory.apply(i), icon)
    }

    var code: String?
        get() = codeArea.text
        set(code) {
            codeArea = CodeArea(code)
        }

    fun setStyleSpans(style: StyleSpans<Collection<String>>) {
        codeArea.setStyleSpans(0, style)
    }

    /**
     *
     * Sett for showing line numbers.
     *
     * @param showLineNumbers whether to show line numbers in the [CodeArea].
     */
    fun setShowLineNumbers(showLineNumbers: Boolean) {
        if (showLineNumbers) {
            codeArea.paragraphGraphicFactory = IntFunction { i: Int -> this.createLinePrefixForLine(i) }
        } else {
            codeArea.paragraphGraphicFactory = null
        }
    }
}
