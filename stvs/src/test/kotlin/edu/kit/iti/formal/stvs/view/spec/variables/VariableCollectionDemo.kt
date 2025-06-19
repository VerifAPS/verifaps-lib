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
package edu.kit.iti.formal.stvs.view.spec.variables

import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.beans.Observable
import javafx.beans.property.SimpleListProperty
import javafx.collections.ListChangeListener
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.control.SplitPane
import javafx.scene.control.TextArea
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import tornadofx.asObservable
import java.util.function.Consumer

/**
 * Created by Philipp on 29.01.2017.
 */
@Tag("demo")
class VariableCollectionDemo {
    @Test
    fun testVariableView() {
        JavaFxTest.runSplitView { this.variableViewScene() }
    }

    private fun variableViewScene(): List<Node?> {
        val types = listOf(
            TypeInt,
            TypeBool,
            TypeEnum("COLORS", mutableListOf("red", "green", "blue")),
        )
        val vars = arrayListOf(FreeVariable("blah", "INT"), FreeVariable("xyz", "BOOL"))
        val varlist = FreeVariableList(vars)

        val controller = VariableCollectionController(SimpleListProperty(types.asObservable()), varlist)

        val rightPane = createExtractedVarsTextArea(controller, controller.validator)

        return listOf(controller.view, rightPane)
    }

    private fun createExtractedVarsTextArea(
        controller: VariableCollectionController,
        validator: FreeVariableListValidator,
    ): Node {
        val textArea = TextArea()
        textArea.styleClass.addAll("model-text-area")
        textArea.isEditable = false

        val set = controller.freeVariableList

        updateText(textArea, set!!.variables)
        set.variables.addListener(
            ListChangeListener { _: ListChangeListener.Change<out FreeVariable?>? ->
                updateText(textArea, set.variables)
            } as ListChangeListener<in FreeVariable?>,
        )

        val problemsArea = TextArea()
        problemsArea.styleClass.addAll("model-text-area")
        textArea.isEditable = false

        updateProblemsText(problemsArea, validator)

        validator.problemsProperty.addListener { _: Observable -> updateProblemsText(problemsArea, validator) }

        val splitPane = SplitPane(textArea, problemsArea)
        splitPane.orientation = Orientation.VERTICAL

        return splitPane
    }

    private fun updateProblemsText(problemsArea: TextArea, validator: FreeVariableListValidator) {
        val error: String =
            validator.problemsProperty.get().entries
                .joinToString("\n") { (k, v) -> "$k -> $v" }
        problemsArea.text = error
    }

    private fun updateText(textArea: TextArea, freeVariables: List<FreeVariable>?) {
        if (freeVariables != null) {
            val output = StringBuilder()
            output.append("Defined free variables:\n")
            freeVariables.forEach(Consumer { type: FreeVariable -> output.append(" - $type\n") })
            textArea.text = output.toString()
        }
    }
}