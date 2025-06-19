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

import edu.kit.iti.formal.stvs.model.table.HybridCell
import edu.kit.iti.formal.stvs.model.table.HybridRow
import edu.kit.iti.formal.stvs.model.table.problems.CellProblem
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import edu.kit.iti.formal.stvs.model.table.problems.DurationProblem
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.beans.Observable
import javafx.scene.control.Label
import javafx.scene.control.Tooltip
import javafx.scene.layout.VBox
import javafx.util.converter.DefaultStringConverter
import java.util.stream.Collectors

/**
 * The view for a cell in a specification table.
 *
 * @author Philipp
 */
class SpecificationTableCell(private val validator: ConstraintSpecificationValidator) : AdvancedTextFieldTableCell<HybridRow?, String?>(DefaultStringConverter()) {
    /**
     * Create a new SpecificationTableCell with a given validator.
     * @param validator The validator for this cell
     */
    init {
        validator.problemsProperty.addListener { _: Observable -> this.onProblemsChanged() }
        emptyProperty().addListener { _: Observable -> this.onProblemsChanged() }
        styleClass.add("spec-cell")
        ViewUtils.setupClass(this)
        onProblemsChanged()
    }

    override fun updateItem(item: String?, empty: Boolean) {
        super.updateItem(item, empty)
        if (!empty && cellModel != null) {
            val counterExampleCells: List<String?>? = cellModel!!.counterExamplesProperty
            val counterExampleLabels = VBox()
            counterExampleLabels.children.addAll(
                counterExampleCells!!.stream().map { text: String? ->
                    val label = Label(text)
                    label.styleClass.add("spec-counterexample")
                    label
                }.collect(Collectors.toList()),
            )
            graphic = counterExampleLabels
        }
    }

    private fun configureProblem(problem: SpecProblem) {
        styleClass.remove("spec-cell-problem")
        styleClass.add("spec-cell-problem")
        tooltip = Tooltip(problem.errorMessage)
    }

    private fun resetCellVisuals() {
        styleClass.remove("spec-cell-problem")
        tooltip = null
    }

    private fun onProblemsChanged() {
        if (!isEmpty) {
            val problems = validator.problems
            for (problem in problems) {
                if (problem is DurationProblem) {
                    if (problem.row == rowIndex) {
                        configureProblem(problem)
                        return
                    }
                }

                if (problem is CellProblem && !isDurationCell) {
                    val col = problem.column
                    if (col == columnId && problem.row == rowIndex) {
                        configureProblem(problem)
                        return
                    }
                }
            }
        }
        resetCellVisuals()
    }

    private val cellModel: HybridCell<*>?
        get() {
            if (tableRow == null) {
                return null
            }
            val row = tableRow.item ?: return null
            val columnId = tableColumn.userData as String?
            return if (columnId != null) {
                row.cells[columnId]
            } else { // we are a duration cell
                row.duration
            }
        }

    private val isDurationCell: Boolean
        get() = tableColumn.userData == null

    private val columnId: String
        get() = tableColumn.userData as String

    private val rowIndex: Int
        get() = tableRow.index
}