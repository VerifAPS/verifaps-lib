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
package edu.kit.iti.formal.stvs.model.common

import tornadofx.getValue
import tornadofx.setValue
import java.util.*

/**
 * This class is used to represent a selected area in a specification table (a col,row-Tuple for a
 * cell, a column, or a row). It is generated (and used) when the user hovers over an area in the
 * timing diagram and represents the corresponding area in the table.
 * @param column The selected column
 * @param row The selected row
 * @author Leon Kaucher
 */
class Selection(column: String? = null, row: Int? = null) {

    val columnProperty = NullableProperty<String?>(column)
    var column: String? by columnProperty

    val rowProperty = NullableProperty<Int?>(row)
    var row: Int? by rowProperty

    private var clickListener = SelectionClickListener { _: String?, _: Int? -> }

    /**
     * Create a new Selection for a given row.
     * @param row The selected row
     */
    constructor(row: Int) : this(null, row)

    /**
     * Specify a listener which is invoked when the user clicks on the selection in the timing
     * diagram. This can be used to trigger changes in the table etc.
     * @param listener The listener to be invoked when the timing diagram is clicked
     */
    fun setOnTimingDiagramSelectionClickListener(listener: SelectionClickListener) {
        this.clickListener = listener
    }

    /**
     * Fire a click event on a given column and row. This invokes the listener specified in
     * [Selection.setOnTimingDiagramSelectionClickListener].
     * @param column The column which was clicked
     * @param row The row which was clicked
     */
    fun fireClickEvent(column: String?, row: Int) {
        clickListener.clicked(column, row)
    }

    /**
     * Turn the selection into an empty selection (i.e. no row/column selected).
     */
    fun clear() {
        rowProperty.set(null)
        columnProperty.set(null)
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj == null || javaClass != obj.javaClass) {
            return false
        }

        val selection = obj as Selection
        if (if (columnProperty.get() == null) {
                selection.columnProperty.get() != null
            } else {
                columnProperty.get() != selection.columnProperty.get()
            }
        ) {
            return false
        }
        return if (rowProperty.get() ==
            null
        ) {
            selection.rowProperty.get() == null
        } else {
            rowProperty.get() == selection.rowProperty.get()
        }
    }

    override fun hashCode(): Int {
        var result = Objects.hashCode(columnProperty.get())
        result = 31 * result + Objects.hashCode(rowProperty.get())
        return result
    }
}