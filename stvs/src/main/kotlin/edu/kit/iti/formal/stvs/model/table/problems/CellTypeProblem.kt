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
package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.Expression
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker
import edu.kit.iti.formal.stvs.model.table.ConstraintCell

/**
 * An instance is created when an [Expression] in a [ConstraintCell] is ill-typed.
 *
 * @author Benjamin Alt
 */
data class CellTypeProblem(val exception: TypeCheckException, override val column: String, override val row: Int) : CellProblem {

    override val errorMessage: String = createErrorMessage(exception)
    override val location: Selection = Selection(column, row)

    companion object {
        /**
         *
         *
         * Either the given expression is well-typed and evaluates to a boolean and is returned, or a
         * [CellTypeProblem] is thrown.
         *
         *
         * @param typeChecker type checker for checking the type of this cell
         * @param columnId the column of the expression to check
         * @param row the row of the expression to check
         * @param expr the expression to type-check for illness / not evaluating to boolean
         * @return an expression that **must** evaluate to true
         * @throws CellTypeProblem a problem if the expression does not evaluate to a boolean or is
         * ill-typed
         */
        @JvmStatic
        @Throws(SpecProblemException::class)
        fun tryTypeCheckCellExpression(
            typeChecker: TypeChecker,
            columnId: String,
            row: Int,
            expr: Expression,
        ): Expression {
            try {
                val type = typeChecker.typeCheck(expr)
                if (type!!.checksAgainst(TypeBool)) {
                    return expr
                } else {
                    throw CellTypeProblem(
                        TypeCheckException(
                            expr,
                            "The cell expression must evaluate to a boolean, " +
                                "instead it evaluates to: " + type.typeName,
                        ),
                        columnId,
                        row,
                    ).asException()
                }
            } catch (typeCheckException: TypeCheckException) {
                throw CellTypeProblem(typeCheckException, columnId, row).asException()
            }
        }

        private fun createErrorMessage(exception: TypeCheckException) = exception.message ?: ""
    }
}