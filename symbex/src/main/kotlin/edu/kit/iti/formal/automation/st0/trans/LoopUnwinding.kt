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
package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.TransformationState

/**
 * Created by weigl on 03/10/14.
 */
class LoopUnwinding : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(LoopUnwindingImpl(state.scope)) as StatementList
        return state
    }

    class LoopUnwindingImpl(private var scope: Scope) : AstMutableVisitor() {
        override fun visit(forStatement: ForStatement): Statement {
            val start = eval(forStatement.start)
            val stop = eval(forStatement.stop)
            var step = 1
            if (forStatement.step != null) {
                step = eval(forStatement.step!!).toInt()
            }

            val loopVariable = forStatement.variable

            val sl = StatementList()

            val replacer = ExpressionReplacer(forStatement.statements) // evtl. clone
            val loopVar: Expression = SymbolicReference(loopVariable)
            var i = start
            while (i < stop) {
                replacer.replacements[loopVar] = IntegerLit(INT, i.toBigInteger())
                sl.addAll(replacer.replace())
                i += step
            }
            return sl
        }

        private fun eval(expr: Expression): Long {
            val iee = IntegerExpressionEvaluator(scope)
            return expr.accept(iee).longValueExact()
        }
    }
}