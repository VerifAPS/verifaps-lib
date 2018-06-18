package edu.kit.iti.formal.automation.st0.trans

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.STSimplifier
import edu.kit.iti.formal.automation.visitors.Visitable

/**
 * Created by weigl on 03/10/14.
 */
class LoopUnwinding : AstMutableVisitor() {
    private lateinit var scope: Scope

    fun defaultVisit(visitable: Visitable): Any {
        return visitable
    }

    override fun visit(localScope: Scope): Scope {
        scope = localScope
        return scope
    }

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
            replacer.replacements[loopVar] = Literal.integer(i.toInt())
            sl.addAll(replacer.replace())
            i += step
        }
        return sl
    }

    private fun eval(expr: Expression): Long {
        val iee = IntegerExpressionEvaluator(scope)
        return expr.accept(iee).longValueExact()
    }

    companion object {
        val transformation = object : ST0Transformation {
            override fun transform(state: STSimplifier.State) {
                val loopUnwinding = LoopUnwinding()
                state.theProgram = state.theProgram!!.accept(loopUnwinding) as ProgramDeclaration
            }
        }
    }
}
