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

import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.smv.ast.SMVExpr

/**
 * @author Alexander Weigl
 * @version 1 (15.04.17)
 */
interface OperationMap {
    fun translateBinaryOperator(left: SMVExpr, operator: BinaryOperator,
                                right: SMVExpr): SMVExpr

    fun translateUnaryOperator(operator: UnaryOperator, sub: SMVExpr): SMVExpr
}
