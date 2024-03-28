package edu.kit.iti.formal.stvs.view.editor

import edu.kit.iti.formal.stvs.Demo
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
import org.junit.experimental.categories.Category
import org.junit.jupiter.api.Test
import java.util.function.Consumer

/**
 * Created by Lukas on 20.01.2017.
 */
@Category(Demo::class)
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
        code.syntaxErrors.forEach(Consumer { error: SyntaxError ->
            output.append(
                " - $error\n"
            )
        })
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
            parsedCode.definedTypes.forEach(Consumer { type: Type ->
                output.append(
                    " - $type\n"
                )
            })
            output.append("\n")
            output.append("\n")
            output.append("Defined IOVariables:\n")
            parsedCode.definedVariables.forEach(Consumer { codeIoVariable: CodeIoVariable ->
                output.append(
                    " - $codeIoVariable\n"
                )
            })
            output.append("SyntaxErrors: \n")
            code.syntaxErrors.forEach(Consumer { syntaxError: SyntaxError ->
                output.append(
                    " - $syntaxError\n"
                )
            })
            textArea.text = output.toString()
        }
    }
}
