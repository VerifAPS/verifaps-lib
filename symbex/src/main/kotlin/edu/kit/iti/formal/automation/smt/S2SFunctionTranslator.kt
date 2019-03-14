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
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.ast.SBinaryOperator
import edu.kit.iti.formal.smv.ast.SFunction
import edu.kit.iti.formal.smv.ast.SUnaryOperator

/**
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
interface S2SFunctionTranslator {
    fun translateOperator(operator: SBinaryOperator, typeLeft: SMVType, rightType: SMVType): SExpr

    fun translateOperator(operator: SUnaryOperator, type: SMVType): SExpr

    fun translateOperator(func: SFunction, args: List<SExpr>): SExpr
}
