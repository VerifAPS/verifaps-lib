package edu.kit.iti.formal.automation.smv.translators

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

import edu.kit.iti.formal.automation.Utils
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*

/**
 * Default translation for ST-Operators.
 *
 * @author Alexander Weigl
 * @version 1 (15.04.17)
 */
class DefaultOperationMap : OperationMap {
    override fun translateBinaryOperator(left: SMVExpr, operator: BinaryOperator, right: SMVExpr): SMVExpr {
        if (operator == SBinaryOperator.DIV) {
            return div(left, right)
        }
        val op = Utils.getSMVOperator(operator)
        return SBinaryExpression(left, op, right)
    }

    override fun translateUnaryOperator(operator: UnaryOperator,
                                        sub: SMVExpr): SMVExpr {
        return SUnaryExpression(Utils.getSMVOperator(operator), sub)
    }

    /**
     * case x/0 := 0
     * else x/y = x div y
     * esac;
     *
     * @param dividend
     * @param divisor
     * @return
     */
    protected fun div(dividend: SMVExpr, divisor: SMVExpr): SMVExpr {
        return SMVFacade.caseexpr(
                divisor.equal(SLiteral.create(0).with(divisor.dataType!!)),
                SLiteral.create(0).with(dividend.dataType!!), SLiteral.TRUE,
                SBinaryExpression(dividend, SBinaryOperator.DIV, divisor))
    }
}
