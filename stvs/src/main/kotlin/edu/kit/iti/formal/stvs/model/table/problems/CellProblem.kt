package edu.kit.iti.formal.stvs.model.table.problems

/**
 * Models problems in cells. Used for rendering in the view (see
 * [edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableCell]).
 *
 * @author Philipp
 */
interface CellProblem : SpecProblem {
    val row: Int
    val column: String
}
