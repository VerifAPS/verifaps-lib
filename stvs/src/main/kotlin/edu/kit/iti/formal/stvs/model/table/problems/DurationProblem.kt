package edu.kit.iti.formal.stvs.model.table.problems

/**
 * The abstract model for problems that occurred in duration cells.
 * @author Philipp
 */
interface DurationProblem : CellProblem{
    override val column: String
        get() = "duration"
}