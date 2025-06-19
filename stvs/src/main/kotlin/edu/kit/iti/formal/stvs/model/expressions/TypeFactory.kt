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
 * Helper class for quickly creating values of [TypeEnum].
 *
 * @author Philipp
 */
object TypeFactory {
    /**
     * Generates an enum type from name and values.
     *
     * @param name the name of the enum type
     * @param values the possible values that this enum type has
     * @return an instance of [TypeEnum]
     */
    fun enumOfName(name: String, vararg values: String): TypeEnum = TypeEnum(name, listOf(*values))
}