/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.model.common

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
private constructor(
    freeVariableName: String,
) : FreeVariableProblem("More than one free variable with name $freeVariableName") {

    override val problemName: String
        get() = "duplicate variable name"

    companion object {
        /**
         * Checks that the given free variable name only occurs once in the given collection, else it
         * returns a [DuplicateFreeVariableProblem].
         * @param freeVariable the free variable to check for duplicates
         * @param allVariables the list of variables that duplicates might be in
         * @return optional of a problem if a duplicate was found or, an empty optional if it wasn't.
         */
        fun checkForDuplicates(
            freeVariable: FreeVariable,
            allVariables: Collection<FreeVariable>,
        ): DuplicateFreeVariableProblem? {
            val varName = freeVariable.name
            return if (isVariableDuplicated(allVariables, varName)) {
                DuplicateFreeVariableProblem(varName)
            } else {
                null
            }
        }

        private fun isVariableDuplicated(allVariables: Collection<FreeVariable>, varName: String): Boolean =
            allVariables.count { it.name == varName } > 1
    }
}