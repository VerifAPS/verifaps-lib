package edu.kit.iti.formal.automation.smv.translators;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.Utils;
import edu.kit.iti.formal.automation.operators.BinaryOperator;
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;
import org.jetbrains.annotations.NotNull;

/**
 * Default translation for ST-Operators.
 *
 * @author Alexander Weigl
 * @version 1 (15.04.17)
 */
public class DefaultOperationMap implements OperationMap {
    @Override public SMVExpr translateBinaryOperator(@NotNull SMVExpr left,
            @NotNull BinaryOperator operator, @NotNull SMVExpr right) {
        if (operator.equals(SBinaryOperator.DIV)) {
            return div(left, right);
        }
        SBinaryOperator op = Utils.getSMVOperator(operator);
        return new SBinaryExpression(left, op, right);
    }

    @NotNull
    @Override public SMVExpr translateUnaryOperator(@NotNull UnaryOperator operator,
                                                    @NotNull SMVExpr sub) {
        return new SUnaryExpression(Utils.getSMVOperator(operator), sub);
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
    protected SMVExpr div(@NotNull SMVExpr dividend, @NotNull SMVExpr divisor) {
        return SMVFacade.INSTANCE.caseexpr(
                divisor.equal(SLiteral.Companion.create(0).as(divisor.getSMVType())),
                SLiteral.Companion.create(0).as(dividend.getSMVType()), SLiteral.Companion.getTRUE(),
                new SBinaryExpression(dividend, SBinaryOperator.DIV, divisor));
    }
}
