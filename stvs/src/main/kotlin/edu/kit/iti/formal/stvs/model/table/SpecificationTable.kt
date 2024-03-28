package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.common.*
import javafx.beans.Observable
import javafx.beans.property.*
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.util.Callback
import org.apache.commons.lang3.StringEscapeUtils
import tornadofx.getValue
import tornadofx.setValue
import java.util.*
import java.util.function.Consumer

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
    name: String?,
    columnHeaderExtractor: Callback<H, Array<Observable>>,
    durationExtractor: Callback<D, Array<Observable>>
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
    var name by nameProperty

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
        durationExtractor: Callback<D, Array<Observable>>
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
            ("Cannot add columns to empty table, add rows first "
                    + "(maybe fill table by rows, instead of by columns)")
        }

        // Check correctness of added column
        val colHeight = column.cells.size
        require(colHeight == rows.size) { "Cannot add column with incorrect height " + colHeight + ", expected: " + rows.size }
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
    fun getOptionalColumnHeaderByName(columnHeaderName: String?): Optional<H> {
        return columnHeaders.stream()
            .filter { specIoVariable: H -> specIoVariable!!.name == columnHeaderName }.findAny()
    }

    /**
     * Get the column header with a given name.
     * @param columnHeaderName The name of the column header
     * @return The corresponding column header
     * @throws NoSuchElementException if there is no such column header
     */
    fun getColumnHeaderByName(columnHeaderName: String?): H {
        return getOptionalColumnHeaderByName(columnHeaderName)
            .orElseThrow {
                NoSuchElementException(
                    "Column does not exist: " + StringEscapeUtils.escapeJava(columnHeaderName)
                )
            }
    }


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
                ("Illegal width for row " + StringEscapeUtils.escapeJava(addedRow.toString())
                        + ", expected width: " + columnHeaders.size)
            }
            require(
                addedRow.cells.keys.stream()
                    .allMatch { columnId: String? -> getOptionalColumnHeaderByName(columnId).isPresent }) {
                ("Added row contains unknown IoVariable: "
                        + StringEscapeUtils.escapeJava(addedRow.toString()))
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
            getOptionalColumnHeaderByName(columnId).ifPresent { otherVariableWithSameName: H ->
                require(
                    otherVariableWithSameName === columnHeader
                ) {
                    ("Cannot add SpecIoVariable that collides with another SpecIoVariable: "
                            + StringEscapeUtils.escapeJava(columnId))
                }
            }
        }
    }

    protected open fun onColumnHeaderRemoved(removed: List<H>) {}

    protected fun onDurationAdded(added: List<D>) {}

    protected fun onDurationRemoved(removed: List<D>) {}

    override fun toString(): String {
        val str = StringBuilder(javaClass.simpleName)
        str.append("\nDurations: ")
        durations.stream().map { obj: D -> obj.toString() }.forEach { string: String? ->
            str.append(string)
            str.append(',')
        }
        str.append("\nColumns: ")
        columnHeaders.stream().map { obj: H -> obj.toString() }.forEach { string: String? ->
            str.append(string)
            str.append(',')
        }
        str.append("\nRows:\n")
        rows.stream().forEachOrdered { row ->
            columnHeaders.forEach(Consumer { header: H ->
                str.append(row!!.cells[header!!.name])
                str.append(',')
            })
            str.append('\n')
        }
        return str.toString()
    }

    companion object {
        const val DEFAULT_NAME: String = "Unnamed Specification"
    }
}
