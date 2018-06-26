package edu.kit.iti.formal.automation

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

import edu.kit.iti.formal.automation.exceptions.OperatorNotFoundException
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.smv.ast.SBinaryOperator
import edu.kit.iti.formal.smv.ast.SUnaryOperator

/**
 * Created by weigl on 26.11.16.
 */
object Utils {
    fun getSMVOperator(operator: BinaryOperator) = when (operator.symbol) {
        "+" -> SBinaryOperator.PLUS
        "-" -> SBinaryOperator.MINUS
        "*" -> SBinaryOperator.MUL
        "/" -> SBinaryOperator.DIV
        "MOD" -> SBinaryOperator.MOD
        "AND" -> SBinaryOperator.AND
        "OR" -> SBinaryOperator.OR
        "<" -> SBinaryOperator.LESS_THAN
        "<=" -> SBinaryOperator.LESS_EQUAL
        ">" -> SBinaryOperator.GREATER_THAN
        ">=" -> SBinaryOperator.GREATER_EQUAL
        "=" -> SBinaryOperator.EQUAL
        "<>" -> SBinaryOperator.NOT_EQUAL
        else -> throw OperatorNotFoundException("Could not find: " + operator.symbol)
    }

    fun getSMVOperator(operator: UnaryOperator) =
            when (operator.symbol) {
                "NOT" -> SUnaryOperator.NEGATE
                "-" -> SUnaryOperator.MINUS
                else -> throw OperatorNotFoundException("Could not find ${operator.symbol}")
            }
}