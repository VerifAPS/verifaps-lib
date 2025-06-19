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
package edu.kit.iti.formal.automation.scope

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.getPromotion
import edu.kit.iti.formal.automation.exceptions.TypeConformityException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.st.ast.*

/**
 * Created by weigl on 26.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class FunctionResolverMUX : FunctionResolver {
    /**
     * {@inheritDoc}
     */
    override fun resolve(call: Invocation, scope: Scope): FunctionDeclaration? {
        if ("MUX" == call.calleeName) {
            val datatypes = call.parameters.map {
                try {
                    call.parameters.map { it.expression.dataType(scope) }
                } catch (variableNotDefinedinScope: VariableNotDefinedException) {
                    variableNotDefinedinScope.printStackTrace()
                } catch (e: TypeConformityException) {
                    e.printStackTrace()
                }
            }
            return createMUXFunctionDeclaration(datatypes as List<AnyDt>)
        }
        return null
    }

    private fun createMUXFunctionDeclaration(datatypes: List<AnyDt>): FunctionDeclaration {
        val fd = FunctionDeclaration(name = "MUX")
        val stmt = CaseStatement()
        fd.returnType.obj = datatypes[1]
        for (i in datatypes.indices) {
            fd.scope.add(
                VariableDeclaration(
                    "a$i",
                    VariableDeclaration.INPUT,
                    datatypes[i],
                ),
            )
            if (i > 0) {
                stmt.addCase(createCase(i))
                fd.returnType.obj = getPromotion(fd.returnType.obj!!, datatypes[i])
            }
        }
        fd.stBody?.add(stmt)
        return fd
    }

    private fun createCase(i: Int): Case {
        val c = Case()
        c.addCondition(CaseCondition.IntegerCondition(IntegerLit(INT, i.toBigInteger())))
        c.statements.add(
            AssignmentStatement(
                SymbolicReference("MUX"),
                SymbolicReference("a$i"),
            ),
        )
        return c
    }
}