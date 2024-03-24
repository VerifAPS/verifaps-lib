package edu.kit.iti.formal.stvs.model.common

import org.apache.commons.lang3.StringEscapeUtils
import java.util.*

/**
 * A [FreeVariableProblem] that occurs when two free variables with the same name occur.
 *
 * @author Philipp
 */
class DuplicateFreeVariableProblem
/**
 * Private constructor: DuplicateFreeVariableProblems can only be created from the static
 * method [DuplicateFreeVariableProblem.checkForDuplicates].
 * @param freeVariableName the name of the duplicate variable
 */
private constructor(freeVariableName: String?) : FreeVariableProblem(
    "More than one free variable with name " + StringEscapeUtils.escapeJava(freeVariableName)
) {
    override val problemName: String
        get() = "duplicate variable name"

    companion object {
        /**
         *
         *
         * Checks that the given free variable name only occurs once in the given collection, else it
         * returns a [DuplicateFreeVariableProblem].
         *
         *
         * @param freeVariable the free variable to check for duplicates
         * @param allVariables the list of variables that duplicates might be in
         * @return optional of a problem if a duplicate was found or, an empty optional if it wasn't.
         */
        fun checkForDuplicates(
            freeVariable: FreeVariable?,
            allVariables: Collection<FreeVariable?>?
        ): Optional<DuplicateFreeVariableProblem> {
            val varName = freeVariable!!.name
            return if (isVariableDuplicated(allVariables, varName)) {
                Optional.of(DuplicateFreeVariableProblem(varName))
            } else {
                Optional.empty()
            }
        }

        private fun isVariableDuplicated(
            allVariables: Collection<FreeVariable?>?,
            varName: String?
        ): Boolean {
            return allVariables!!.stream().filter { otherVar: FreeVariable? -> otherVar!!.name == varName }.count() > 1
        }
    }
}
