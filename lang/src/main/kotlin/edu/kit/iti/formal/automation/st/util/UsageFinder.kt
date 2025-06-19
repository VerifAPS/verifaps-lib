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
package edu.kit.iti.formal.automation.st.util

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.AssignmentStatement
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.util.info
import java.util.*

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 */
class UsageFinder : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}

    val knownVariables
        get() = writtenReferences + readReference

    val writtenReferences = HashSet<SymbolicReference>()
    val readReference = HashSet<SymbolicReference>()

    override fun visit(assignmentStatement: AssignmentStatement) {
        writtenReferences.add(assignmentStatement.location)
        assignmentStatement.expression.accept(this)
    }

    override fun visit(localScope: Scope) {
        writtenReferences.clear()
        readReference.clear()
    }

    override fun visit(symbolicReference: SymbolicReference) {
        readReference.add(symbolicReference)
    }

    companion object {
        fun investigate(visitable: Visitable): UsageFinder {
            val waf = UsageFinder()
            visitable.accept(waf)
            return waf
        }

        /**
         * Given an executable instance (scope, stcode). This method:
         * * removes the unused variables
         * * sets input flag accordingly to only read variables
         * * sets the output flag accordingly to only written variables
         *
         * Writes information to console.
         */
        fun markVariablesByUsage(simplified: PouExecutable, default: Int = 0) {
            val fuv = UsageFinder.investigate(simplified)

            val unused = fuv.knownVariables.toHashSet()
            unused.removeAll(fuv.writtenReferences)
            unused.removeAll(fuv.readReference)
            val unusedS = unused.map { it.identifier }

            val onlyWritten = fuv.writtenReferences.toHashSet()
            onlyWritten.removeAll(fuv.readReference)

            val onlyRead = fuv.readReference.toHashSet()
            onlyRead.removeAll(fuv.writtenReferences)

            info("Remove unused ${unusedS.size} variables:")
            unusedS.forEach { info("\t$it") }
            simplified.scope.variables.removeAllByName(unusedS)

            val onlyWrittenS = onlyWritten.map { it.identifier }
            val onlyReadS = onlyRead.map { it.identifier }

            info("Promote only written variables to outputs (${onlyWritten.size}):")
            onlyWrittenS.forEach { info("\t$it") }

            info("Promote only read variables to inputs (${onlyRead.size}):")
            onlyReadS.forEach { info("\t$it") }

            simplified.scope.variables.forEach {
                if (it.name in onlyReadS) {
                    it.type = VariableDeclaration.INPUT
                } else {
                    if (it.name in onlyWrittenS) {
                        it.type = VariableDeclaration.OUTPUT
                    } else {
                        it.type = default
                    }
                }
            }
        }
    }
}
