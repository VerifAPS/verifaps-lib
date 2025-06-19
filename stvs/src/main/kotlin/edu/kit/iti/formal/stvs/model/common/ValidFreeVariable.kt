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

import edu.kit.iti.formal.stvs.model.expressions.Expression
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.Value

/**
 * A valid free variable. Its name is a valid identifier, its type is a parsed [Type]
 * object (instead of Strings denoting only the type name) and its value is a parsed
 * [Value] object of the respective type.
 *
 *
 * Create a new ValidFreeVariable with a given name, type and default value.
 * @param name The name of this FreeVariable
 * @param type The type of this FreeVariable
 * @param constraint constraint expression for this global variable
 *
 * @author Philipp
 */
data class ValidFreeVariable(val name: String, val type: Type, val constraint: Expression?) {
    fun asIOVariable(): ValidIoVariable = ValidIoVariable(VariableCategory.INPUT, name, type, VariableRole.ASSUME)
}