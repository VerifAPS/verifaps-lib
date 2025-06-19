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

import edu.kit.iti.formal.stvs.model.expressions.ValueBool.Companion.of

/**
 * Created by philipp on 17.01.17.
 */
object SimpleExpressions {
    fun negate(e: Expression): Expression = UnaryFunctionExpr(UnaryFunctionExpr.Op.UNARY_MINUS, e)

    fun not(e: Expression): Expression = UnaryFunctionExpr(UnaryFunctionExpr.Op.NOT, e)

    fun and(e1: Expression, e2: Expression): Expression = BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, e1, e2)

    fun plus(e1: Expression, e2: Expression): Expression = BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, e1, e2)

    fun minus(e1: Expression, e2: Expression): Expression = BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, e1, e2)

    fun equal(e1: Expression, e2: Expression): Expression = BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, e1, e2)

    fun lessThan(e1: Expression, e2: Expression): Expression =
        BinaryFunctionExpr(BinaryFunctionExpr.Op.LESS_THAN, e1, e2)

    fun lessEqual(e1: Expression, e2: Expression): Expression =
        BinaryFunctionExpr(BinaryFunctionExpr.Op.LESS_EQUALS, e1, e2)

    fun greaterEqual(e1: Expression, e2: Expression): Expression =
        BinaryFunctionExpr(BinaryFunctionExpr.Op.GREATER_EQUALS, e1, e2)

    fun variable(name: String): Expression = VariableExpr(name)

    fun variable(name: String, index: Int): Expression = VariableExpr(name, index)

    fun literal(integer: Int): Expression = LiteralExpr(ValueInt(integer))

    fun literal(bool: Boolean): Expression = LiteralExpr(of(bool))

    fun literal(e: ValueEnum): Expression = LiteralExpr(e)

    fun literalEnum(value: String, sourceType: TypeEnum): Expression = literal(ValueEnum(value, sourceType))
}