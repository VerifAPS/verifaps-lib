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
 * A problem concerning [FreeVariable]s.
 *
 * @author Philipp
 */
abstract class FreeVariableProblem
/**
 * Construct a new FreeVariableProblem with a given error message.
 * @param errorMessage The error message
 */
protected constructor(
    /**
     * Get the error message of this FreeVariableProblem.
     * @return The error message
     */
    @JvmField val errorMessage: String?,
) : Exception() {
    val guiMessage: String
        /**
         *
         * This method can be used for showing text in the gui.
         *
         * @return a message suited for a dialog in the view
         */
        get() = problemName + ": " + errorMessage

    abstract val problemName: String
}