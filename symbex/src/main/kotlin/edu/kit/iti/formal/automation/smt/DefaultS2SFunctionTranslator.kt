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
package edu.kit.iti.formal.automation.smt

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SSymbol
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.SMVWordType
import edu.kit.iti.formal.smv.ast.SBinaryOperator
import edu.kit.iti.formal.smv.ast.SFunction
import edu.kit.iti.formal.smv.ast.SUnaryOperator
import java.util.*

/**
 * http://smtlib.cs.uiowa.edu/Logics/QF_BV.smt2
 *
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
class DefaultS2SFunctionTranslator : S2SFunctionTranslator {

    override fun translateOperator(operator: SBinaryOperator, typeLeft: SMVType?, rightType: SMVType?): SExpr {
        val defaultValue = "not-found-operator-${operator.symbol()}-$typeLeft-$rightType"

        val lookup = when (typeLeft) {
            is SMVWordType -> {
                val (signed) = typeLeft
                if (signed) {
                    bvsOperators
                } else {
                    bvuOperators
                }
            }
            is EnumType -> bvuOperators
            SMVTypes.INT -> arithOperators
            else -> logicalOperators
        }
        val value = lookup[operator] ?: defaultValue
        return SSymbol(value)
    }

    override fun translateOperator(operator: SUnaryOperator, type: SMVType?): SExpr {
        val bvneg = SSymbol("bvneg")
        val not = SSymbol("not")
        return when (operator) {
            SUnaryOperator.MINUS -> bvneg
            SUnaryOperator.NEGATE -> not
        }
    }

    override fun translateOperator(func: SFunction, args: List<SExpr>): SExpr = TODO("translation of various functions")

    companion object {
        internal var logicalOperators: MutableMap<SBinaryOperator, String> = EnumMap(SBinaryOperator::class.java)
        internal var bvuOperators: MutableMap<SBinaryOperator, String> = EnumMap(SBinaryOperator::class.java)
        internal var bvsOperators: MutableMap<SBinaryOperator, String> = EnumMap(SBinaryOperator::class.java)
        internal var arithOperators: MutableMap<SBinaryOperator, String> = EnumMap(SBinaryOperator::class.java)

        init {
            logicalOperators[SBinaryOperator.AND] = "and"
            logicalOperators[SBinaryOperator.OR] = "or"
            logicalOperators[SBinaryOperator.IMPL] = "impl"
            logicalOperators[SBinaryOperator.EQUAL] = "="
            logicalOperators[SBinaryOperator.NOT_EQUAL] = "xor"
            logicalOperators[SBinaryOperator.XOR] = "xor"
            logicalOperators[SBinaryOperator.XNOR] = "="

            bvsOperators[SBinaryOperator.MUL] = "bvmul"
            bvsOperators[SBinaryOperator.PLUS] = "bvadd"
            bvsOperators[SBinaryOperator.DIV] = "bvsdiv"
            bvsOperators[SBinaryOperator.XOR] = "bvxor"
            bvsOperators[SBinaryOperator.XNOR] = "bvxnor"
            bvsOperators[SBinaryOperator.EQUAL] = "="
            bvsOperators[SBinaryOperator.MINUS] = "bvsub"
            bvsOperators[SBinaryOperator.MOD] = "bvsmod"
            bvsOperators[SBinaryOperator.GREATER_EQUAL] = "bvsge"
            bvsOperators[SBinaryOperator.GREATER_THAN] = "bvsgt"
            bvsOperators[SBinaryOperator.LESS_EQUAL] = "bvsle"
            bvsOperators[SBinaryOperator.LESS_THAN] = "bvslt"
            bvsOperators[SBinaryOperator.NOT_EQUAL] = "<>"

            bvuOperators[SBinaryOperator.NOT_EQUAL] = "<>"
            bvuOperators[SBinaryOperator.MUL] = "bvmul"
            bvuOperators[SBinaryOperator.PLUS] = "bvadd"
            bvuOperators[SBinaryOperator.DIV] = "bvudiv"
            bvuOperators[SBinaryOperator.XOR] = "bvxor"
            bvuOperators[SBinaryOperator.EQUAL] = "="
            bvuOperators[SBinaryOperator.XNOR] = "bvxnor"
            bvuOperators[SBinaryOperator.MINUS] = "bvsub"
            bvuOperators[SBinaryOperator.MOD] = "bvurem"
            bvuOperators[SBinaryOperator.GREATER_EQUAL] = "bvuge"
            bvuOperators[SBinaryOperator.GREATER_THAN] = "bvugt"
            bvuOperators[SBinaryOperator.LESS_EQUAL] = "bvule"
            bvuOperators[SBinaryOperator.LESS_THAN] = "bvult"

            arithOperators[SBinaryOperator.NOT_EQUAL] = "distinct"
            arithOperators[SBinaryOperator.MUL] = "*"
            arithOperators[SBinaryOperator.PLUS] = "+"
            arithOperators[SBinaryOperator.DIV] = "div"
            arithOperators[SBinaryOperator.XOR] = "xor"
            arithOperators[SBinaryOperator.EQUAL] = "="
            // arithOperators[SBinaryOperator.XNOR] = ""
            arithOperators[SBinaryOperator.MINUS] = "-"
            arithOperators[SBinaryOperator.MOD] = "mod"
            arithOperators[SBinaryOperator.GREATER_EQUAL] = ">="
            arithOperators[SBinaryOperator.GREATER_THAN] = ">"
            arithOperators[SBinaryOperator.LESS_EQUAL] = "<="
            arithOperators[SBinaryOperator.LESS_THAN] = "<"
        }
    }
}
