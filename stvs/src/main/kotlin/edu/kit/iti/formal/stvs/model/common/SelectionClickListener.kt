package edu.kit.iti.formal.stvs.model.common

/**
 * `SelectionClickListener` gets invoked by [Selection] and indicates that the user
 * clicked on a view (such as a region in a timing diagram) that represents a cell in the
 * [edu.kit.iti.formal.stvs.model.table.HybridSpecification].
 */
fun interface SelectionClickListener {
    /**
     * Must handle a click event that can be assigned to a cell in a
     * [edu.kit.iti.formal.stvs.model.table.HybridSpecification]
     *
     * @param columnName Name of the column that the event can be assigned to
     * @param rowNumber Number of the row that the event can be assigned to
     */
    fun clicked(columnName: String?, rowNumber: Int?)
}
