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

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.table.problems.ColumnProblem
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.beans.binding.Bindings
import javafx.geometry.Pos
import javafx.scene.control.Label
import javafx.scene.control.Tooltip
import javafx.scene.layout.HBox
import javafx.scene.layout.VBox
import java.util.*

/**
 *
 *
 * This is the view for the column headers inside a specification table view. The underlying linked
 * model are [SpecIoVariable]s.
 *
 *
 * @author Philipp
 */
class ColumnHeader(specIoVariable: SpecIoVariable) : VBox() {
    val categoryLabel: Label = Label(specIoVariable.category.toString())
    val columnNameLabel: Label = Label(specIoVariable.name)
    val columnTypeLabel: Label = Label(specIoVariable.type)
    private val typeOfLabel = Label(" : ")
    private val varDescriptionHbox: HBox
    private val problemTooltip = Tooltip("")

    /**
     *
     *
     * Creates the view for the given [SpecIoVariable] as model.
     *
     *
     * @param specIoVariable the model for this view.
     */
    init {
        ViewUtils.setupClass(this)

        categoryLabel.textProperty().bind(Bindings.convert(specIoVariable.categoryProperty))
        columnNameLabel.textProperty().bind(specIoVariable.nameProperty)
        columnTypeLabel.textProperty().bind(specIoVariable.typeProperty)

        val inout = specIoVariable.category.toString().lowercase(Locale.getDefault())

        categoryLabel.styleClass.addAll("spec-column-header", "category-label", inout)
        columnNameLabel.styleClass.addAll("spec-column-header", "name-label")
        columnTypeLabel.styleClass.addAll("spec-column-header", "type-label")
        typeOfLabel.styleClass.addAll("spec-column-header", "type-of-label")
        problemTooltip.styleClass.addAll("spec-column-header", "problem-tooltip")

        specIoVariable.categoryProperty
            .addListener { o, oldCategory, category -> this.updateInOutClass(oldCategory, category) }

        styleClass.addAll("spec-column-header", inout)
        this.alignment = Pos.CENTER

        this.varDescriptionHbox = HBox(columnNameLabel, typeOfLabel, columnTypeLabel)
        varDescriptionHbox.alignment = Pos.CENTER

        children.addAll(categoryLabel, varDescriptionHbox)
    }

    private fun updateInOutClass(oldCategory: VariableCategory?, category: VariableCategory?) {
        val old = oldCategory.toString().lowercase(Locale.getDefault())
        val newCategory = category.toString().lowercase(Locale.getDefault())
        styleClass.remove(old)
        styleClass.add(newCategory)

        categoryLabel.styleClass.remove(old)
        categoryLabel.styleClass.add(newCategory)
    }

    /**
     *
     *
     * Sets the tooltip and classes for the given collection of column problems of this class.
     *
     *
     *
     *
     * This will configure <tt>spec-column-problem</tt> as a css class.
     *
     *
     * @param problems the list of problems. If there should not be any problems viewed, then use the
     * method [.resetProblems] instead.
     */
    fun configureProblems(problems: Collection<ColumnProblem>) {
        styleClass.remove("spec-column-problem")
        styleClass.add("spec-column-problem")
        problemTooltip.text = problems.joinToString("\n") { it.errorMessage ?: "" }
        Tooltip.install(this, problemTooltip)
    }

    fun resetProblems() {
        styleClass.remove("spec-column-problem")
        Tooltip.uninstall(this, problemTooltip)
    }
}