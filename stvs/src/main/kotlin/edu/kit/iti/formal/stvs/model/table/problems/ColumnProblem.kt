package edu.kit.iti.formal.stvs.model.table.problems

/**
 * A [SpecProblem] concerning columns.
 *
 * @author Philipp
 */
interface ColumnProblem : SpecProblem {
    val column: String
}
