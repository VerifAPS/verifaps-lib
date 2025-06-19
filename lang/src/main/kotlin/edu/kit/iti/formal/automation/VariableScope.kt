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
package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.st.SetLookupList
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 */
typealias VariableScope = SetLookupList<VariableDeclaration>

/*data class VariableScope(
        private val impl: LinkedHashMap<String, VariableDeclaration> = linkedMapOf())
    : MutableMap<String, VariableDeclaration> by impl, Cloneable<VariableScope>, Serializable {

    fun add(variable: VariableDeclaration) {
        put(variable.name, variable)
    }

    override fun clone(): VariableScope {
        val vs = VariableScope()
        forEach({ s, v -> vs.put(s, v.clone() as VariableDeclaration) })
        return vs
    }
}*/
