package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.Demo
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.beans.Observable
import javafx.beans.property.SimpleListProperty
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.control.Button
import javafx.scene.control.SplitPane
import javafx.scene.control.TextArea
import javafx.scene.layout.Pane
import javafx.scene.layout.Priority
import javafx.scene.layout.VBox
import org.apache.commons.io.IOUtils
import org.junit.jupiter.api.Test
import org.junit.experimental.categories.Category
import tornadofx.asObservable
import java.io.*
import java.util.*
import java.util.function.Supplier

/**
 * Created by Philipp on 01.02.2017.
 */
@Category(Demo::class)
class SpecificationTableDemo {
    @Test
    fun testTable() {
        JavaFxTest.Companion.runSplitView(Supplier<List<Node?>> { this.simpleTableScene() })
    }

    private fun simpleTableScene(): List<Node?> {
        val types = listOf(TypeInt.INT, TypeBool.BOOL)
        val codevars = listOf(
            CodeIoVariable(VariableCategory.INPUT, "BOOL", "A"),
            CodeIoVariable(VariableCategory.INPUT, "INT", "B"),
            CodeIoVariable(VariableCategory.OUTPUT, "INT", "C")
        )
        val typeContext = SimpleListProperty(types.asObservable())
        val codeIoVariables = SimpleListProperty(codevars.asObservable())

        val freeVariableList = FreeVariableList(ArrayList())

        val freevarValidator = FreeVariableListValidator(typeContext, freeVariableList)
        val table = SpecificationTableController(
            GlobalConfig(),
            typeContext,
            codeIoVariables,
            freevarValidator.validFreeVariablesProperty,
            HybridSpecification(freeVariableList, true)
        )
        val extractedTablePane = createExtractedTableTextArea(
            table.hybridSpecification!!,
            table.validator
        )

        return listOf<Node?>(table.view, extractedTablePane)
    }

    private fun createExtractedTableTextArea(
        spec: ConstraintSpecification,
        recognizer: ConstraintSpecificationValidator
    ): Pane {
        val textArea = TextArea()
        textArea.styleClass.addAll("model-text-area")
        textArea.isEditable = false

        updateText(textArea, spec)

        val updateButton = Button("Refresh")
        updateButton.onAction = EventHandler { event: ActionEvent? -> updateText(textArea, spec) }

        val problemsArea = TextArea()
        problemsArea.styleClass.addAll("model-text-area")
        textArea.isEditable = false

        updateProblemsText(problemsArea, recognizer)

        recognizer.problemsProperty().addListener { o: Observable? -> updateProblemsText(problemsArea, recognizer) }

        val splitPane = SplitPane(textArea, problemsArea)
        splitPane.orientation = Orientation.VERTICAL
        VBox.setVgrow(splitPane, Priority.ALWAYS)
        return VBox(updateButton, splitPane)
    }

    private fun updateProblemsText(problemsArea: TextArea, recognizer: ConstraintSpecificationValidator) {
        val error = recognizer.problemsProperty().get()
            .joinToString("\n") { (it?.javaClass?.simpleName ?: "") + ": " + (it?.errorMessage ?: "") }
        problemsArea.text = error
    }

    private fun updateText(textArea: TextArea, spec: ConstraintSpecification) {
        try {
            //ExporterFacade.exportSpec(spec)
            //val output = IOUtils.toString(stream.toByteArray(), "UTF-8")
            //textArea.text = output
        } catch (e: Exception) {
            val writeString = StringWriter()
            e.printStackTrace(PrintWriter(writeString))
            e.printStackTrace()
            textArea.text = writeString.toString()
        }
    }
}