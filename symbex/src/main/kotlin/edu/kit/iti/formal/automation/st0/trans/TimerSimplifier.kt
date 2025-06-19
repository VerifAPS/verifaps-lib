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

import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import java.math.BigInteger

/**
 * @author Alexander Weigl (06.07.2014), Augusto Modanese
 * @version 1
 */
class TimerSimplifier(val cycleTime: Long = DEFAULT_CYCLE_TIME) : MultiCodeTransformation() {
    init {
        transformations += TimeLiteralToCounter()
    }

    inner class TimeLiteralToCounter :
        AstMutableVisitor(),
        CodeTransformation {
        override fun transform(state: TransformationState): TransformationState {
            state.stBody = state.stBody.accept(this) as StatementList
            state.scope = state.scope.accept(this) as Scope
            return state
        }

        override fun visit(vd: VariableDeclaration): VariableDeclaration {
            if (vd.dataType === TimeType.TIME_TYPE) {
                val newVariable = VariableDeclaration(vd.name, vd.type, UINT)
                val cycles = (vd.init as TimeLit?)
                val sd = SimpleTypeDeclaration(
                    baseType = RefTo(UINT),
                    initialization = translate(cycles),
                )
                newVariable.typeDeclaration = sd
                return newVariable
            }
            return super.visit(vd)
        }

        override fun visit(literal: Literal) = when (literal) {
            is TimeLit -> translate(literal)
            else -> super.visit(literal)
        }

        private fun translate(literal: TimeLit?): IntegerLit {
            if (literal == null) {
                return IntegerLit(UINT, BigInteger.ZERO)
            }
            val value = literal.asValue()
            val data = value.value
            val cycles = (data.milliseconds / cycleTime).toInt()
            return IntegerLit(UINT, cycles.toBigInteger())
        }
    }

    companion object {
        var DEFAULT_CYCLE_TIME: Long = 4
    }
}