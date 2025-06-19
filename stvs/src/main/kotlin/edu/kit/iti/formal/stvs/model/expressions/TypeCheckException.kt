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
 * An Exception for type errors. Occurs when one wants to parse an [Expression] like
 * <tt>2 AND TRUE</tt> or <tt>42 = FALSE</tt>.
 *
 * @author Philipp
 */
class TypeCheckException
/**
 * Create a new TypeCheckException.
 * @param mistypedExpression the expression that is ill-typed. This would be the whole expression
 * (for example <tt>2 AND TRUE</tt>)
 * @param message a message about what went wrong.
 */
(
    /**
     * Get the expression for which this TypeCheckException was thrown.
     * @return the expression that is ill-typed. This would be the whole expression (for example
     * <tt>2 AND TRUE</tt>)
     */
    val mistypedExpression: Expression?,
        message: String?
) : Exception(
    "$message\nIn Expression: $mistypedExpression"
) {
    override fun hashCode(): Int = if (mistypedExpression != null) mistypedExpression.hashCode() else 0

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val that = o as TypeCheckException

        return if (mistypedExpression != null) mistypedExpression == that.mistypedExpression else that.mistypedExpression == null
    }

    companion object {
        private const val serialVersionUID = 1L
    }
}