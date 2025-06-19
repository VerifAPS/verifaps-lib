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
package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleStringProperty
import javafx.collections.FXCollections
import tornadofx.getValue
import tornadofx.setValue

/**
 *
 * The model for a cell (for
 * [edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableCell])
 * that both has an abstract cell model, a [CellOperationProvider] (that is, either a
 * [ConstraintCell] or [ConstraintDuration]), and a list of counterexample
 * strings that should be viewed in-place below these cells.
 *
 * @author Philipp
 */
class HybridCell<C : CellOperationProvider?>(val cell: C) : CellOperationProvider {
    val counterExamplesProperty = SimpleListProperty(FXCollections.observableArrayList<String>())
    var counterExamples by counterExamplesProperty

    override val commentProperty = SimpleStringProperty()
    override val stringRepresentationProperty = SimpleStringProperty()

    /**
     * Makes all counterexample cells disappear. After this call
     * <tt>[.counterExamplesProperty].isEmpty()</tt> is true.
     */
    fun clearCounterExample() {
        counterExamplesProperty.setAll()
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as HybridCell<*>

        if (asString != other.asString) return false
        if (comment != other.comment) return false
        if (counterExamples != other.counterExamples) return false

        return true
    }

    override fun hashCode(): Int {
        var result = asString.hashCode()
        result = 31 * result + comment.hashCode()
        result = 31 * result + counterExamples.hashCode()
        return result
    }
}