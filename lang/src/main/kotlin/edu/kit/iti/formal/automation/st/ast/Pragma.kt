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
package edu.kit.iti.formal.automation.st.ast

import edu.kit.iti.formal.automation.st.Cloneable
import kotlin.reflect.full.findAnnotation

annotation class PragmaType(val default: String = "")

sealed class Pragma : Cloneable {
    val kind: String
        get() = this.javaClass.getAnnotation(PragmaType::class.java)?.default ?: ""
    abstract override fun clone(): Pragma

    @PragmaType("attribute")
    data class Attribute(var parameters: MutableMap<String, String> = hashMapOf()) : Pragma() {
        var name: String = parameters["#0"]!!
        override fun clone(): Pragma = copy()
    }
}

/**
 *
 */

fun makePragma(type: String, parameters: MutableMap<String, String>): Pragma? {
    Pragma::class.nestedClasses.forEach {
        val a = it.findAnnotation<PragmaType>()?.default
        if (type == a) {
            return it.constructors.first().call(parameters) as Pragma
        }
    }
    return null
}