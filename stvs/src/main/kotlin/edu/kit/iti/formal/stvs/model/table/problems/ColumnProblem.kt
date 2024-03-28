package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection

/**
 * A [SpecProblem] concerning columns.
 *
 * @author Philipp
 */
abstract class ColumnProblem
/**
 * Create a new ColumnProblem with a given error message and for a given column.
 * @param errorMessage The error message
 * @param column The header name of the problematic column
 */(errorMessage: String?, @JvmField val column: String?) : SpecProblem(
    errorMessage, Selection(
        column
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

        val that = obj as ColumnProblem

        return if (column != null) column == that.column else that.column == null
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + (if (column != null) column.hashCode() else 0)
        return result
    }
}
