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
package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation for boolean types.
 * This is a singleton since this class does not have any state.
 *
 * @author Philipp
 */
object TypeBool : Type {
    override fun checksAgainst(other: Type): Boolean =
        other.match({ false }, { true }, { otherEnum: TypeEnum? -> false })!!

    override val typeName: String
        get() = "BOOL"

    override fun parseLiteral(literal: String): Value? {
        if ("true".equals(literal, ignoreCase = true)) {
            return ValueBool.TRUE
        }
        if ("false".equals(literal, ignoreCase = true)) {
            return ValueBool.FALSE
        }
        return null
    }

    override fun generateDefaultValue(): Value = ValueBool.FALSE

    override fun toString(): String = "TypeBool"
}