package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection

/**
 * Models problems in cells. Used for rendering in the view (see
 * [edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableCell]).
 *
 * @author Philipp
 */
open class CellProblem
/**
 * Constructor for a problem that has an error message and a position inside a table.
 *
 * @param errorMessage the error message
 * @param column the column of the problematic cell
 * @param row the row of the problematic cell
 */(errorMessage: String?, @JvmField val column: String?, @JvmField val row: Int) : SpecProblem(
    errorMessage, Selection(
        column, row
    )
) {
    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj == null || javaClass != obj.javaClass) {
            return false
        }
        if (!super.equals(obj)) {
            return false
        }

        val that = obj as CellProblem

        if (row != that.row) {
            return false
        }
        return if (column != null) column == that.column else that.column == null
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + row
        result = 31 * result + (if (column != null) column.hashCode() else 0)
        return result
    }
}
