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
package edu.kit.iti.formal.stvs.view.editor

import edu.kit.iti.formal.stvs.model.code.SyntaxError
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.control.Label
import javafx.scene.control.ListView
import javafx.scene.control.SplitPane
import javafx.scene.control.Tooltip
import javafx.scene.layout.HBox
import org.fxmisc.richtext.CodeArea
import org.fxmisc.richtext.LineNumberFactory
import org.fxmisc.richtext.model.StyleSpans
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon
import java.util.function.IntFunction

/**
 * The view for the left side of our application: The code editor.
 *
 * This view contains both the [CodeArea] for editing the code and the [ListView] for
 * viewing a list of syntax errors. It itself extends a [SplitPane] for combining these two
 * views.
 *
 * @author csicar on 09.01.17.
 * @author Lukas Fritsch
 */
class EditorPane @JvmOverloads constructor(
    code: String = "",
    val syntaxErrors: ObservableList<SyntaxError>,
    showLineNumbers: Boolean = true,
) : SplitPane() {

    var codeArea: CodeArea

    private val lineNumberFactory: IntFunction<Node>

    /**
     * Creates an editable EditorPane with the given code as initial source code text.
     * @param code the string to initialize the [CodeArea] to
     * @param syntaxErrors the initial list of [SyntaxError]s.
     * @param showLineNumbers whether to show line numbers in the [CodeArea]
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
        val icon = Label(null, FontIcon(FontAwesomeSolid.EXCLAMATION_CIRCLE))
        val lineSyntaxErrors = syntaxErrors.filtered { it.line == i + 1 }.filterNotNull()
        setLineIcon(i, lineSyntaxErrors, icon)
        syntaxErrors.addListener { _: ListChangeListener.Change<*> ->
            setLineIcon(i, lineSyntaxErrors, icon)
        }
        return HBox(lineNumberFactory.apply(i), icon)
    }

    var code: String
        get() = codeArea.text
        set(value) {
            codeArea.clear()
            codeArea.insertText(0, value)
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