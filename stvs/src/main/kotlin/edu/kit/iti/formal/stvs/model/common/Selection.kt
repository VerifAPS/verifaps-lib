package edu.kit.iti.formal.stvs.model.common

import java.util.*

/**
 * This class is used to represent a selected area in a specification table (a col,row-Tuple for a
 * cell, a column, or a row). It is generated (and used) when the user hovers over an area in the
 * timing diagram and represents the corresponding area in the table.
 *
 * @author Leon Kaucher
 */
class Selection {
    private var column: NullableProperty<String?>
    private var row: NullableProperty<Int?>
    private var clickListener = SelectionClickListener { s: String?, i: Int? -> }

    /**
     * Create a new Selection for a given column and row.
     * @param column The selected column
     * @param row The selected row
     */
    constructor(column: String?, row: Int) {
        this.column = NullableProperty(column)
        this.row = NullableProperty(row)
    }

    /**
     * Create a new Selection for a given column.
     * @param column The selected column
     */
    constructor(column: String?) {
        this.column = NullableProperty(column)
        this.row = NullableProperty()
    }

    /**
     * Create a new Selection for a given row.
     * @param row The selected row
     */
    constructor(row: Int) {
        this.column = NullableProperty()
        this.row = NullableProperty(row)
    }

    /**
     * Create a new empty selection ("nothing was selected").
     */
    constructor() {
        this.column = NullableProperty()
        this.row = NullableProperty()
    }

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

    fun getColumn(): Optional<String> {
        return Optional.ofNullable(column.get())
    }

    fun columnProperty(): NullableProperty<String?> {
        return column
    }

    fun setColumn(column: String?) {
        this.column.set(column)
    }

    fun getRow(): Optional<Int> {
        return Optional.ofNullable(row.get())
    }

    fun rowProperty(): NullableProperty<Int?> {
        return row
    }

    fun setRow(row: Int) {
        this.row.set(row)
    }

    /**
     * Turn the selection into an empty selection (i.e. no row/column selected).
     */
    fun clear() {
        row.set(null)
        column.set(null)
    }


    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj == null || javaClass != obj.javaClass) {
            return false
        }

        val selection = obj as Selection
        if (if (column.get() == null) selection.column.get() != null
            else column.get() != selection.column.get()
        ) {
            return false
        }
        return if (row.get() == null) selection.row.get() == null else row.get() == selection.row.get()
    }

    override fun hashCode(): Int {
        var result = Objects.hashCode(column.get())
        result = 31 * result + Objects.hashCode(row.get())
        return result
    }
}
