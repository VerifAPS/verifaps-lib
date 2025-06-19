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

import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty

/**
 * A cell containing constraint expression (for the syntax, see
 * https://git.scc.kit.edu/peese/stverificationstudio/issues/25). The cells in a
 * [ConstraintSpecification] are of this type.
 *
 * @author Benjamin Alt
 */
class ConstraintCell(stringRepresentation: String?) : CellOperationProvider {
    override val stringRepresentationProperty: StringProperty = SimpleStringProperty(stringRepresentation)
    override val commentProperty: StringProperty = SimpleStringProperty()

    constructor(constraintCell: ConstraintCell?) : this(constraintCell!!.asString) {
        comment = constraintCell.comment
    }

    override fun toString() = debuggingString()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as ConstraintCell

        if (asString != other.asString) return false
        if (comment != other.comment) return false

        return true
    }

    override fun hashCode(): Int {
        var result = asString.hashCode()
        result = 31 * result + comment.hashCode()
        return result
    }
}