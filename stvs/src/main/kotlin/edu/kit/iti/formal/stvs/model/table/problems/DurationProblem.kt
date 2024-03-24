package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection

/**
 *
 *
 * The abstract model for problems that occurred in duration cells.
 *
 *
 * @author Philipp
 */
abstract class DurationProblem
/**
 *
 *
 * Creates a duration problem with given error message (used for error tooltips in the GUI).
 *
 *
 * @param errorMessage the error message (used for viewing error tooltips)
 * @param row the row in which the problem occurred
 */(errorMessage: String?, @JvmField val row: Int) : SpecProblem(errorMessage, Selection("duration", row)) {
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

        val that = obj as DurationProblem

        return row == that.row
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + row
        return result
    }
}
