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
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException
import edu.kit.iti.formal.stvs.model.table.ConstraintCell

/**
 *
 *
 * A problem that is generated when a ConstraintCell inside a Constraint/HybridSpecification cannot
 * be parsed correctly (i.e. according to the antlr grammar file in <tt>src/main/antlr</tt>).
 *
 *
 * @author Benjamin Alt
 */
data class CellParseProblem(val exception: ParseException, override val column: String, override val row: Int) : CellProblem {
    override val errorMessage: String = createErrorMessage(exception)
    override val location: Selection = Selection(column, row)
    val parseException: ParseException = exception

    companion object {
        /**
         * Tries to create an [Expression] from the given string and context information.
         *
         * @param typeContext the type context needed for parsing enums
         * @param columnId the column of the cell to check
         * @param row the row of the cell to check
         * @param cell the cell to parse
         * @return an [Expression]-AST (that might still be ill-typed)
         * @throws CellParseProblem if the expression could not be parsed
         * @throws CellUnsupportedExpressionProblem if the expression contains unsupported grammar
         * features (for example function calls)
         */
        @Throws(SpecProblemException::class)
        fun tryParseCellExpression(
            typeContext: List<Type>,
            columnId: String,
            row: Int,
            cell: ConstraintCell,
        ): Expression {
            val parser = ExpressionParser(columnId, typeContext)
            try {
                return parser.parseExpression(cell.asString ?: "")
            } catch (parseException: ParseException) {
                throw CellParseProblem(parseException, columnId, row).asException()
            } catch (unsupportedException: UnsupportedExpressionException) {
                throw CellUnsupportedExpressionProblem(unsupportedException, columnId, row).asException()
            }
        }

        private fun createErrorMessage(exception: ParseException): String = exception.message ?: ""
    }
}