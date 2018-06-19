package edu.kit.iti.formal.automation.st0.trans

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import java.math.BigInteger

/**
 * Created by weigl on 03/10/14.
 */
class IntegerExpressionEvaluator(private val scope: Scope) : AstVisitor<BigInteger>() {
    override fun defaultVisit(obj: Any) = BigInteger.ZERO

    override fun visit(binaryExpression: BinaryExpression): BigInteger {
        val op = binaryExpression.operator

        val left = binaryExpression.leftExpr.accept(this)
        val right = binaryExpression.rightExpr.accept(this)

        if (op === Operators.ADD)
            return left + right
        if (op === Operators.DIV)
            return left / right
        if (op === Operators.SUB)
            return left - right
        if (op === Operators.MULT)
            return left * right

        Console.error("Unsupported operation %s", op)
        return left
    }

    override fun visit(unaryExpression: UnaryExpression): BigInteger {
        val op = unaryExpression.operator
        val left = unaryExpression.expression.accept(this)

        if (op === Operators.MINUS)
            return -left

        Console.error("Unsupported operation %s", op)
        return left
    }

    override fun visit(literal: Literal): BigInteger {
        return when (literal) {
            is IntegerLit -> literal.value
            else -> BigInteger.ZERO
        }
    }

    override fun visit(symbolicReference: SymbolicReference): BigInteger {
        val id = symbolicReference.identifier
        val vd = scope.getVariable(symbolicReference)
        // ScalarValue sv = (ScalarValue) vd.getInit();
        try {
            return BigInteger.ZERO//sv.getValue();
        } catch (e: ClassCastException) {
            Console.error("%s isType not a integer variable", id)
            return BigInteger.ZERO
        }

    }
}
