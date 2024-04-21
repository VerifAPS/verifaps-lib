package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException

/**
 * The cell problem analog to the [UnsupportedExpressionException]. Created when expressions
 * with function calls or if guards or similar are encountered which have not yet been implemented.
 *
 * @author Benjamin Alt
 */
data class CellUnsupportedExpressionProblem(
    val exception: UnsupportedExpressionException,
    override val column: String, override val row: Int
) : CellProblem {

    override val errorMessage: String = exception.message ?: ""
    override val location = Selection(column, row)
}
