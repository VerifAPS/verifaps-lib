package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection

/**
 * A problem concerning a specification table.
 * @author Philipp
 */
sealed interface SpecProblem {
    val errorMessage: String
    val location: Selection

    fun asException() = SpecProblemException(this)
}

data class SpecProblemException(val problem: SpecProblem) : Exception(problem.errorMessage)
