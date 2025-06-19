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

import edu.kit.iti.formal.stvs.TestUtils.loadCodeFromFile
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.code.SyntaxError
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.scene.Node
import javafx.scene.control.TextArea
import javafx.scene.layout.Pane
import javafx.scene.layout.StackPane
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import java.util.function.Consumer

/**
 * Created by Lukas on 20.01.2017.
 */
@Tag("demo")
class EditorDemo {
    @Test
    fun javaFxTest() {
        JavaFxTest.runSplitView { this.editorAndModelSplit() }
    }

    private fun editorAndModelSplit(): List<Node> {
        val code: Code = loadCodeFromFile("define_type.st")
        val controller = EditorPaneController(code, GlobalConfig())

        val rightPane = createExtractedVarsTextArea(code)

        return listOf<Node>(controller.view, rightPane)
    }

    private fun updateSyntaxErrors(textField: TextArea, code: Code) {
        val output = StringBuilder()
        output.append("Syntax-Errors:\n")
        code.syntaxErrors.forEach(
            Consumer { error: SyntaxError ->
                output.append(
                    " - $error\n",
                )
            },
        )
        textField.text = output.toString()
    }

    private fun createExtractedVarsTextArea(code: Code): Pane {
        val textArea = TextArea()
        textArea.styleClass.addAll("model-text-area")
        textArea.isEditable = false

        updateText(textArea, code)
        code.parsedCodeProperty.addListener { ob, old, parsedCode -> updateText(textArea, code) }

        return StackPane(textArea)
    }

    private fun updateText(textArea: TextArea, code: Code) {
        val parsedCode = code.parsedCode
        if (parsedCode != null) {
            val output = StringBuilder()
            output.append("Defined types:\n")
            parsedCode.definedTypes.forEach(
                Consumer { type: Type ->
                    output.append(
                        " - $type\n",
                    )
                },
            )
            output.append("\n")
            output.append("\n")
            output.append("Defined IOVariables:\n")
            parsedCode.definedVariables.forEach(
                Consumer { codeIoVariable: CodeIoVariable ->
                    output.append(
                        " - $codeIoVariable\n",
                    )
                },
            )
            output.append("SyntaxErrors: \n")
            code.syntaxErrors.forEach(
                Consumer { syntaxError: SyntaxError ->
                    output.append(
                        " - $syntaxError\n",
                    )
                },
            )
            textArea.text = output.toString()
        }
    }
}