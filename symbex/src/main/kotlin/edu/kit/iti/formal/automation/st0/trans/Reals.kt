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

import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.AnyReal
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import edu.kit.iti.formal.automation.datatypes.values.VAnyReal
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import java.math.BigDecimal

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.07.18)
 */
class RealToInt(factor: Int = 1, intDataType: AnyInt = INT) : MultiCodeTransformation() {
    init {
        transformations += RewriteRealDeclaration(factor, intDataType)
        transformations += RewriteRealConversions(factor, intDataType)
        transformations += RemoveConversionCalls()
    }
}

class RemoveConversionCalls : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(RemoveConversionCallsImpl) as StatementList
        return state
    }

    object RemoveConversionCallsImpl : AstMutableVisitor() {
        val regexToInt = "l?real_to_.{0,2}int".toRegex(RegexOption.IGNORE_CASE)
        val regexToReal = ".{0,2}int_to_l?real".toRegex(RegexOption.IGNORE_CASE)
        override fun visit(invocation: Invocation): Expression {
            val name = invocation.callee.identifier
            val b = regexToInt.matchEntire(name) != null || regexToReal.matchEntire(name) != null

            if (b) {
                return invocation.parameters[0].expression
            } else {
                return invocation
            }
        }
    }
}

class RewriteRealDeclaration(val factor: Int, val intDataType: AnyInt) : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.scope.variables.forEach {
            if (it.dataType == AnyReal.REAL) {
                rewriteRealDecl(it)
            }
            if (it.dataType == AnyReal.LREAL) {
                rewriteLRealDecl(it)
            }
        }
        return state
    }

    private fun rewriteRealDecl(it: VariableDeclaration) {
        it.dataType = intDataType
        it.typeDeclaration =
            SimpleTypeDeclaration(intDataType, rewriteRealLiteral(factor, intDataType, it.init as RealLit?))
        rewriteRealLiteral(factor, intDataType, it)
    }

    private fun rewriteLRealDecl(it: VariableDeclaration) {
        val dt = intDataType.next() ?: intDataType
        it.dataType = dt
        it.typeDeclaration = SimpleTypeDeclaration(dt, rewriteRealLiteral(factor, dt, it.init as RealLit?))
        rewriteRealLiteral(factor, dt, it)
    }
}

private fun rewriteRealLiteral(factor: Int, dt: AnyInt, lit: RealLit?): IntegerLit? = if (lit == null) {
    null
} else {
    IntegerLit(rewriteRealLiteral(factor, dt, lit.value))
}

private fun rewriteRealLiteral(factor: Int, dataType: AnyInt, value: VariableDeclaration) {
    if (value.initValue != null) {
        val (dt, v) = value.initValue as VAnyReal
        value.initValue = rewriteRealLiteral(factor, dataType, v)
    }
}

private fun rewriteRealLiteral(factor: Int, dataType: AnyInt, value: BigDecimal): VAnyInt =
    VAnyInt(dataType, value.multiply(BigDecimal(factor)).toBigInteger())

class RewriteRealConversions(val factor: Int, val intDataType: AnyInt) : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(RealLiteralRewriter()) as StatementList
        return state
    }

    inner class RealLiteralRewriter : AstMutableVisitor() {
        override fun visit(literal: Literal): Expression = when (literal) {
            is RealLit -> {
                rewriteRealLiteral(factor, intDataType, literal)!!
            }
            else -> literal
        }
    }
}