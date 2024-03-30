package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection

/**
 * A [SpecProblem] concerning columns.
 *
 * @author Philipp
 */
interface ColumnProblem : SpecProblem {
    val column: String
}
