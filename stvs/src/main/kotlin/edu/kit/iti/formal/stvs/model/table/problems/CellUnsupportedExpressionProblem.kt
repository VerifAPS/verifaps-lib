package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException

/**
 * The cell problem analog to the [UnsupportedExpressionException]. Created when expressions
 * with function calls or if guards or similar are encountered which have not yet been implemented.
 *
 * @author Benjamin Alt
 */
class CellUnsupportedExpressionProblem(
    exception: UnsupportedExpressionException, column: String?,
    row: Int
) : CellProblem(createErrorMessage(exception), column, row) {
    val unsupportedExpression: UnsupportedExpressionException? = exception

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

        val that = obj as CellUnsupportedExpressionProblem

        return if (unsupportedExpression != null) unsupportedExpression == that.unsupportedExpression else that.unsupportedExpression == null
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + (if (unsupportedExpression != null) unsupportedExpression.hashCode() else 0)
        return result
    }

    companion object {
        private fun createErrorMessage(exception: UnsupportedExpressionException): String? {
            return exception.message
        }
    }
}
