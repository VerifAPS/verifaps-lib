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

import edu.kit.iti.formal.stvs.model.common.Named
import javafx.beans.Observable
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.util.Callback
import tornadofx.getValue
import tornadofx.setValue
import java.util.*

/**
 * A specification table.
 *
 * @param <H> The column header type
 * @param <C> The cell type
 * @param <D> The duration type
 *
 * @author Benjamin Alt
 * @author Philipp
</D></C></H> */
open class SpecificationTable<H : Named?, C, D>(
    name: String = "unnamed",
    columnHeaderExtractor: Callback<H, Array<Observable>>,
    durationExtractor: Callback<D, Array<Observable>>,
) {

    /**
     * Get the SpecIoVariables for this table, i.e. the column headers.
     * You should **not mutate** this list. For adding new columns, use
     * [SpecificationTable.addColumn].
     * @return the list of SpecIoVariables
     */
    var columnHeaders: ObservableList<H> = FXCollections.observableArrayList(columnHeaderExtractor)
    var rows: ObservableList<SpecificationRow<C>> =
        FXCollections.observableArrayList { specificationRow: SpecificationRow<C> -> arrayOf(specificationRow) }
    var durations: ObservableList<D> = FXCollections.observableArrayList(durationExtractor)

    val nameProperty: StringProperty = SimpleStringProperty(name)
    var name: String by nameProperty

    /**
     * Construct a new SpecificationTable with a default name, no rows or columns and the specified
     * column header and row extractors. These are needed for "deep observing" and are used to
     * indicate to observable collections such as [ObservableList] which properties of the
     * items in the collection should cause change events on the collection itself.
     * See also
     * [this post](http://stackoverflow.com/questions/31687642/callback-and-extractors-for-javafx-observablelist)
     * on why and how extractors are used.
     * @param columnHeaderExtractor The extractor for the column headers
     * @param durationExtractor The extractor for the duration headers
     */
    constructor(
        columnHeaderExtractor: Callback<H, Array<Observable>>,
        durationExtractor: Callback<D, Array<Observable>>,
    ) : this(DEFAULT_NAME, columnHeaderExtractor, durationExtractor)

    /**
     * Construct a new SpecificationTable with a given name, no rows or columns and the specified
     * column header and row extractors. These are needed for "deep observing" and are used to
     * indicate to observable collections such as [ObservableList] which properties of the
     * items in the collection should cause change events on the collection itself.
     * See also
     * [
 * this post](http://stackoverflow.com/questions/31687642/callback-and-extractors-for-javafx-observablelist) on why and how extractors are used.
     * @param name name of this specification
     * @param columnHeaderExtractor The extractor for the column headers
     * @param durationExtractor The extractor for the duration headers
     */
    init {
        rows.addListener { change: ListChangeListener.Change<out SpecificationRow<C>> -> this.onRowChange(change) }
        columnHeaders.addListener { change: ListChangeListener.Change<out H> -> this.onColumnHeadersChanged(change) }
        durations.addListener { change: ListChangeListener.Change<out D> -> this.onDurationChange(change) }
    }

    /**
     * Return the column whose header has the given name.
     * @param columnHeaderName The name of the column header
     * @return The corresponding column
     * @throws NoSuchElementException if the column header does not exist
     */
    fun getColumnByName(columnHeaderName: String): SpecificationColumn<C> {
        val columnHeader = getColumnHeaderByName(columnHeaderName)
        val cells = rows.mapNotNull { row: SpecificationRow<C> -> row.cells[columnHeader?.name] }
        return SpecificationColumn(cells)
    }

    /**
     * Remove and return the column whose header has the given name.
     * @param columnHeaderName The name of the column header
     * @return The corresponding column (which was deleted from the table)
     * @throws NoSuchElementException if the column header does not exist
     */
    fun removeColumnByName(columnHeaderName: String): SpecificationColumn<C> {
        val column = getColumnByName(columnHeaderName)
        columnHeaders.remove(getColumnHeaderByName(columnHeaderName))
        for (row in rows) {
            row!!.cells.remove(columnHeaderName)
        }
        onColumnRemoved(column)
        return column
    }

    /**
     * Add a column with a given column header to the specification table.
     * @param columnHeader The column header for the column to be added
     * @param column The column to add
     * @throws IllegalArgumentException if the column header already exists in the specification table
     * @throws IllegalStateException if the table does not have any rows yet. First fill a table by
     * rows, then add columns if necessary/desired.
     * @throws IllegalArgumentException if the column height does not correspond to the number of
     * rows already in the table.
     */
    fun addColumn(columnHeader: H, column: SpecificationColumn<C?>) {
        // throws IllegalArgumentException if a var with same name already exists:
        columnHeaders.add(columnHeader)

        check(rows.size != 0) {
            (
                "Cannot add columns to empty table, add rows first " +
                    "(maybe fill table by rows, instead of by columns)"
                )
        }

        // Check correctness of added column
        val colHeight = column.cells.size
        require(colHeight == rows.size) {
            "Cannot add column with incorrect height " + colHeight + ", expected: " +
                rows.size
        }
        for (row in rows.indices) {
            rows[row]!!.cells[columnHeader!!.name] = column.cells[row]
        }
        onColumnAdded(column)
    }

    /**
     * Get the column header with a given name.
     * @param columnHeaderName The name of the column header
     * @return An [Optional] containing the corresponding column header or an
     * empty [Optional] there is no such header
     */
    fun getOptionalColumnHeaderByName(columnHeaderName: String?): H? =
        columnHeaders.find { it!!.name == columnHeaderName }

    /**
     * Get the column header with a given name.
     * @param columnHeaderName The name of the column header
     * @return The corresponding column header
     * @throws NoSuchElementException if there is no such column header
     */
    fun getColumnHeaderByName(columnHeaderName: String?): H = getOptionalColumnHeaderByName(columnHeaderName)
        ?: throw NoSuchElementException("Column does not exist: $columnHeaderName")

    /**
     * Invoked when the list of row changes.
     * @param change The [javafx.collections.ListChangeListener.Change] object corresponding
     * to the list change
     */
    protected fun onRowChange(change: ListChangeListener.Change<out SpecificationRow<C>>) {
        while (change.next()) {
            if (change.wasPermutated()) {
                onRowOrderChanged()
            }
            if (change.wasAdded()) {
                onRowAdded(change.addedSubList)
            }
            if (change.wasRemoved()) {
                onRowRemoved(change.removed)
            }
        }
    }

    /**
     * Invoked when the list of column headers changes.
     * @param change The [javafx.collections.ListChangeListener.Change] object corresponding
     * to the list change
     */
    protected fun onColumnHeadersChanged(change: ListChangeListener.Change<out H>) {
        while (change.next()) {
            if (change.wasAdded()) {
                onColumnHeaderAdded(change.addedSubList)
            }
            if (change.wasRemoved()) {
                onColumnHeaderRemoved(change.removed)
            }
        }
    }

    /**
     * Invoked when the list of durations changes.
     * @param change The [javafx.collections.ListChangeListener.Change] object corresponding
     * to the list change
     */
    protected fun onDurationChange(change: ListChangeListener.Change<out D>) {
        while (change.next()) {
            if (change.wasAdded()) {
                onDurationAdded(change.addedSubList)
            }
            if (change.wasRemoved()) {
                onDurationRemoved(change.removed)
            }
        }
    }

    protected fun onRowAdded(added: List<SpecificationRow<C>?>) {
        for (addedRow in added) {
            // Check correctness of added row
            require(addedRow!!.cells.size == columnHeaders.size) {
                "Illegal width for row $addedRow, expected width: ${columnHeaders.size}"
            }
            require(addedRow.cells.keys.all { getOptionalColumnHeaderByName(it) != null }) {
                "Added row contains unknown IoVariable: $addedRow"
            }
        }
    }

    protected fun onRowRemoved(removed: List<SpecificationRow<C>?>?) {}

    protected fun onRowOrderChanged() {}

    protected fun onColumnAdded(column: SpecificationColumn<C?>?) {}

    protected fun onColumnRemoved(column: SpecificationColumn<C>) {}

    protected open fun onColumnHeaderAdded(added: List<H>) {
        for (columnHeader in added) {
            val columnId = columnHeader!!.name
            getOptionalColumnHeaderByName(columnId)?.let {
                require(it === columnHeader) {
                    "Cannot add SpecIoVariable that collides with another SpecIoVariable: $columnId"
                }
            }
        }
    }

    protected open fun onColumnHeaderRemoved(removed: List<H>) {}

    protected fun onDurationAdded(added: List<D>) {}

    protected fun onDurationRemoved(removed: List<D>) {}

    override fun toString(): String = buildString {
        append(javaClass.simpleName)
        append("\nDurations: ")
        durations.joinTo(this, ", ") { it.toString() }
        append("\nColumns: ")
        columnHeaders.joinTo(this, ", ") { it.toString() }
        append("\nRows:\n")
        /*rows.joinTo(this, "\n") { row ->
            columnHeaders.joinTo(this, ",") { header ->
                row!!.cells[header!!.name].toString()
            }
        }*/
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as SpecificationTable<*, *, *>

        if (columnHeaders != other.columnHeaders) return false
        if (rows != other.rows) return false
        if (durations != other.durations) return false
        if (name != other.name) return false

        return true
    }

    override fun hashCode(): Int {
        var result = columnHeaders.hashCode()
        result = 31 * result + rows.hashCode()
        result = 31 * result + durations.hashCode()
        result = 31 * result + name.hashCode()
        return result
    }

    companion object {
        const val DEFAULT_NAME: String = "Unnamed Specification"
    }
}