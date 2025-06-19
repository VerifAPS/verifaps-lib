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
 * The runtime-representation for parsed, binary function expressions. Examples are: +, -, =, AND,
 * OR, etc. Anything that has two arguments.
 * @param operation the [Op] that this expression should do with its arguments.
 * @param firstArgument the first (or left) argument
 * @param secondArgument the second (or right) argument
 * @author Philipp
 */
data class BinaryFunctionExpr(val operation: Op, val firstArgument: Expression, val secondArgument: Expression) : Expression() {
    enum class Op {
        // (BOOL, BOOL) -> BOOL
        AND,
        OR,
        XOR,

        // (INT, INT) -> BOOL
        GREATER_THAN,
        GREATER_EQUALS,
        LESS_THAN,
        LESS_EQUALS,

        // (a, a) -> BOOL
        EQUALS,
        NOT_EQUALS,

        // (INT, INT) -> INT
        PLUS,
        MINUS,
        MULTIPLICATION,
        DIVISION,
        MODULO,
        POWER,
    }

    override fun <R> accept(visitor: ExpressionVisitor<R>): R = visitor.visitBinaryFunction(this)

    override fun toString(): String = "Bin($firstArgument $operation $secondArgument)"
}