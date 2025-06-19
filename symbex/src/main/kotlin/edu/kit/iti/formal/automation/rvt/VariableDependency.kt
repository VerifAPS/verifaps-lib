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
package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.smv.SMVAstDefaultVisitor
import edu.kit.iti.formal.smv.ast.*
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
class VariableDependency(private val state: SymbolicState) {
    fun dependsOn(names: Collection<VariableDeclaration>, ignoredVars: List<VariableDeclaration>): Set<SVariable> {
        val reached = names.map { SymbExFacade.asSVariable(it) }.toHashSet()
        val ignored = ignoredVars.map { SymbExFacade.asSVariable(it) }.toSet()
        val vv = VarVisitor(reached, ignored)

        // fixpoint
        var changed = false
        do {
            val backup = LinkedList(reached)
            for (name in backup) {
                val e = state[name]
                e?.accept(vv)
            }
            changed = backup.size != reached.size
        } while (changed)

        return reached
    }

    internal class VarVisitor(private val reached: MutableSet<SVariable>, private val ignored: Set<SVariable>) : SMVAstDefaultVisitor<Unit>() {

        override fun visit(top: SMVAst) {
        }

        override fun visit(v: SVariable) {
            if (!ignored.contains(v)) {
                reached.add(v)
            }
        }

        override fun visit(be: SBinaryExpression) {
            be.left.accept(this)
            be.right.accept(this)
        }

        override fun visit(ue: SUnaryExpression) {
            ue.expr.accept(this)
        }

        override fun visit(l: SLiteral) {
        }

        override fun visit(a: SAssignment) {
        }

        override fun visit(ce: SCaseExpression) {
            for ((condition, then) in ce.cases) {
                condition.accept(this)
                then.accept(this)
            }
        }

        override fun visit(smvModule: SMVModule) {
        }

        override fun visit(func: SFunction) {
            func.arguments.forEach { a -> a.accept(this) }
        }
    }
}