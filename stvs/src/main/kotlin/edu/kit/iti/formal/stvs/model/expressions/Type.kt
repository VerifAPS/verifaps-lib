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
 * The super-interface for all Types.
 *
 * @author Philipp
 */
sealed interface Type {
    /**
     * matches the actual type present. Subclasses call the correct function.
     *
     * @param matchIntType in case its a [TypeInt]
     * @param matchBoolType in case its a [TypeBool]
     * @param matchEnumType in case its a [TypeEnum]
     * @param <R> the return type of the visitor
     * @return the return value of the visitor
     </R> */
    fun <R> match(
        matchIntType: TypeIntegerHandler<R>,
        matchBoolType: TypeBooleanHandler<R>,
        matchEnumType: TypeEnumHandler<R>,
    ): R = when (this) {
        is TypeBool -> matchBoolType.handle()
        is TypeInt -> matchIntType.handle()
        is TypeEnum -> matchEnumType.handle(this)
    }

    /**
     * Finds out whether this type checks against another type, which means any value of this type can
     * be used as a value of the other type.
     * This mostly means type equality or a supertype relation.
     *
     * @param other the other type ot subsume.
     * @return whether it does subsume the other type or not.
     */
    fun checksAgainst(other: Type): Boolean

    /**
     * Get the type name of this type in a human-readable format (in contrast to this classes'
     * toString()). This can be used to show the type in a GUI, for example.
     *
     * @return a string that should match the type name as it is usually used in st-code.
     */
    val typeName: String

    /**
     * Parse a literal of this type to a value. Can be used for parsing user-input into TextFields
     * when the type is known, for example.
     *
     * @param literal the literal string to parse
     * @return optionally a resulting value
     */
    fun parseLiteral(literal: String): Value?

    /**
     * For any <tt>[Type] type</tt> the following must be true:
     * <tt>type.generateDefaultValue().getErrorType().checksAgainst(type)</tt>
     *
     * @return a default value of this given type.
     */
    fun generateDefaultValue(): Value
}