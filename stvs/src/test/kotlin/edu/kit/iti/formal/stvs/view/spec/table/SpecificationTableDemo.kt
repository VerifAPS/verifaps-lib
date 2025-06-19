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
package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
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
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import tornadofx.asObservable
import java.io.PrintWriter
import java.io.StringWriter

/**
 * Created by Philipp on 01.02.2017.
 */
@Tag("demo")
class SpecificationTableDemo {
    @Test
    fun testTable() {
        JavaFxTest.runSplitView { this.simpleTableScene() }
    }

    private fun simpleTableScene(): List<Node?> {
        val types = listOf(TypeInt, TypeBool)
        val codevars = listOf(
            CodeIoVariable(VariableCategory.INPUT, "BOOL", "A"),
            CodeIoVariable(VariableCategory.INPUT, "INT", "B"),
            CodeIoVariable(VariableCategory.OUTPUT, "INT", "C"),
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
            HybridSpecification(freeVariableList, true),
        )
        val extractedTablePane = createExtractedTableTextArea(
            table.hybridSpecification!!,
            table.validator,
        )

        return listOf<Node?>(table.view, extractedTablePane)
    }

    private fun createExtractedTableTextArea(
        spec: ConstraintSpecification,
        recognizer: ConstraintSpecificationValidator,
    ): Pane {
        val textArea = TextArea()
        textArea.styleClass.addAll("model-text-area")
        textArea.isEditable = false

        updateText(textArea, spec)

        val updateButton = Button("Refresh")
        updateButton.onAction = EventHandler { _: ActionEvent -> updateText(textArea, spec) }

        val problemsArea = TextArea()
        problemsArea.styleClass.addAll("model-text-area")
        textArea.isEditable = false

        updateProblemsText(problemsArea, recognizer)

        recognizer.problemsProperty.addListener { _: Observable -> updateProblemsText(problemsArea, recognizer) }

        val splitPane = SplitPane(textArea, problemsArea)
        splitPane.orientation = Orientation.VERTICAL
        VBox.setVgrow(splitPane, Priority.ALWAYS)
        return VBox(updateButton, splitPane)
    }

    private fun updateProblemsText(problemsArea: TextArea, recognizer: ConstraintSpecificationValidator) {
        val error = recognizer.problemsProperty.get()
            .joinToString("\n") { (it?.javaClass?.simpleName ?: "") + ": " + (it?.errorMessage ?: "") }
        problemsArea.text = error
    }

    private fun updateText(textArea: TextArea, spec: ConstraintSpecification) {
        try {
            val output = edu.kit.iti.formal.stvs.logic.io.xml.TestUtils.stringOutputStream {
                ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.XML, it)
            }
            textArea.text = output
        } catch (e: Exception) {
            val writeString = StringWriter()
            e.printStackTrace(PrintWriter(writeString))
            e.printStackTrace()
            textArea.text = writeString.toString()
        }
    }
}