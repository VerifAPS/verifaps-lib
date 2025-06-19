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
package edu.kit.iti.formal.stvs.view.spec.variables.clipboard

import edu.kit.iti.formal.stvs.model.common.FreeVariable

/**
 * This class handles the conversion from a list of [FreeVariable] to JSON and vice versa.
 *
 * @author Philipp
 */
object Json {
    var json = Json

    /**
     * Generates JSON from variables.
     * @param freeVariables variables to convert
     * @return Stringified JSON version of variables
     */
    fun stringFromRealFreeVariables(freeVariables: List<FreeVariable>): String {
        return "" // return json.encodeToString(fromRealFreeVariables(freeVariables))
    }

    /**
     * Generates variables from JSON.
     * @param input Stringified JSON version of variables
     * @return restored variables
     */
    fun stringToRealFreeVariables(input: String?): List<FreeVariable> {
        // if (input == null)
        return listOf()
        // return toRealFreeVariables(json.decodeFromString<FreeVarSelection>(input))
    }

    /**
     * Generates a stringifyable [FreeVarSelection] from a list of [FreeVariable].
     * @param freeVariables variables to convert
     * @return converted selection
     */
    fun fromRealFreeVariables(freeVariables: List<FreeVariable>): FreeVarSelection {
        val vars = freeVariables.map { FreeVar(it.name, it.type, it.constraint) }
        return FreeVarSelection(vars)
    }

    /**
     * Generates a list of [FreeVariable] from the stringifyable class [FreeVarSelection].
     *
     * @param selection stringifyable selection
     * @return list of variables
     */
    fun toRealFreeVariables(selection: FreeVarSelection): List<FreeVariable> =
        selection.selected.map { FreeVariable(it.name, it.type, it.defaultval) }

    data class FreeVarSelection(var selected: List<FreeVar> = listOf())

    data class FreeVar(var name: String? = null, var type: String? = null, var defaultval: String? = null)
}