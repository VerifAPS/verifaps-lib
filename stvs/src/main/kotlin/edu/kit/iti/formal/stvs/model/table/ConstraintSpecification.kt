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

import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import javafx.beans.Observable
import javafx.beans.property.SimpleStringProperty
import javafx.beans.value.ChangeListener
import javafx.util.Callback

/**
 * A specification the cell contents and durations of which are specified by constraints rather than
 * concrete values. This corresponds to a "generalized test table".
 *
 * @author Benjamin Alt
 */
open class ConstraintSpecification(name: String, val freeVariableList: FreeVariableList) :
    SpecificationTable<SpecIoVariable, ConstraintCell, ConstraintDuration>(
        name,
        Callback<SpecIoVariable, Array<Observable>> { columnHeader: SpecIoVariable ->
            arrayOf(columnHeader.nameProperty, columnHeader.typeProperty, columnHeader.categoryProperty)
        },
        Callback<ConstraintDuration, Array<Observable>> { durationCell: ConstraintDuration ->
            arrayOf(durationCell.stringRepresentationProperty, durationCell.commentProperty)
        },
    ),
    Commentable {

    override val commentProperty = SimpleStringProperty()
    private val onSpecIoVariableNameChanged: ChangeListener<String?>

    /**
     * Construct a new, empty ConstraintSpecification with a default name from an initial list of free
     * variables.
     *
     * @param freeVariableList The initial list of free variables
     */
    constructor(freeVariableList: FreeVariableList) : this(DEFAULT_NAME, freeVariableList)

    /**
     * Construct a new, empty ConstraintSpecification with a given name and an initial list of free
     * variables.
     *
     * @param name The name of the ConstraintSpecification
     * @param freeVariableList The list of free variables
     */
    init {
        this.onSpecIoVariableNameChanged =
            ChangeListener<String?> { _, nameBefore, nameAfter ->
                this.onSpecIoVariableNameChanged(nameBefore, nameAfter)
            }
    }

    /**
     * Copy constructor. Creates a deep copy of another ConstraintSpecification.
     *
     * @param sourceSpec The ConstraintSpecification to copy
     */
    constructor(sourceSpec: ConstraintSpecification) : this(
        sourceSpec.name,
        FreeVariableList(sourceSpec.freeVariableList),
    ) {
        comment = sourceSpec.comment

        for (specIoVariable in sourceSpec.columnHeaders) {
            columnHeaders.add(SpecIoVariable(specIoVariable))
        }
        for (row in sourceSpec.rows) {
            val clonedCells = hashMapOf<String, ConstraintCell>()
            for (colHeader in row!!.cells.keys) {
                clonedCells[colHeader] = ConstraintCell(row.cells[colHeader])
            }
            val clonedRow = SpecificationRow(clonedCells, row.extractor)
            clonedRow.comment = row.comment
            rows.add(clonedRow)
        }
        for (sourceDuration in sourceSpec.durations) {
            durations.add(ConstraintDuration(sourceDuration))
        }
    }

    override fun onColumnHeaderAdded(added: List<SpecIoVariable>) {
        super.onColumnHeaderAdded(added)
        added.forEach { specIoVariable: SpecIoVariable -> this.subscribeToIoVariable(specIoVariable) }
    }

    override fun onColumnHeaderRemoved(removed: List<SpecIoVariable>) {
        super.onColumnHeaderRemoved(removed)
        removed.forEach { specIoVariable: SpecIoVariable -> this.unsubscribeFromIoVariable(specIoVariable) }
    }

    /**
     * Add a listener for name changes to a given `SpecIoVariable`.
     *
     * @param specIoVariable The SpecIoVariable to add a name change listener to
     */
    private fun subscribeToIoVariable(specIoVariable: SpecIoVariable) {
        specIoVariable.nameProperty.addListener(onSpecIoVariableNameChanged)
    }

    /**
     * Remove a listener for name changes from a given `SpecIoVariable`.
     *
     * @param specIoVariable The SpecIoVariable to remove a listener from
     */
    private fun unsubscribeFromIoVariable(specIoVariable: SpecIoVariable) {
        specIoVariable.nameProperty.removeListener(onSpecIoVariableNameChanged)
    }

    private fun onSpecIoVariableNameChanged(nameBefore: String?, nameAfter: String?) {
        for (row in rows) {
            val entry = row!!.cells[nameBefore]
            if (entry != null) {
                row.cells[nameAfter] = entry
                row.cells.remove(nameBefore)
            }
        }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as ConstraintSpecification

        if (freeVariableList != other.freeVariableList) return false
        if (comment != other.comment) return false
        if (name != other.name) return false
        if (rows != other.rows) return false
        if (durations != other.durations) return false
        if (columnHeaders != other.columnHeaders) return false

        return true
    }

    override fun hashCode(): Int {
        var result = freeVariableList.hashCode()
        result = 31 * result + comment.hashCode()
        result = 31 * result + columnHeaders.hashCode()
        result = 31 * result + name.hashCode()
        result = 31 * result + rows.hashCode()
        result = 31 * result + durations.hashCode()
        return result
    }

    override fun toString(): String = super.toString()

    companion object {
        /**
         * Construct a new specification row containing ConstraintCells.
         *
         * @param initialCells The initial cells, a Map from column identifier to ConstraintCell, with
         * which to fill the new row
         * @return A SpecificationRow containing the given ConstraintCells
         */
        fun createRow(initialCells: Map<String, ConstraintCell>): SpecificationRow<ConstraintCell> =
            SpecificationRow(initialCells) { cell: ConstraintCell ->
                arrayOf(cell.stringRepresentationProperty, cell.commentProperty)
            }
    }
}