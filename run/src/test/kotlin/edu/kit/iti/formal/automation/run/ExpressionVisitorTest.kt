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
package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import edu.kit.iti.formal.automation.datatypes.values.VBool
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.AssignmentStatement
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.visitors.Visitable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

class ExpressionVisitorTest {
    @Test
    fun basicTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("expressionVisitorTest.basicTest.st"))
        IEC61131Facade.resolveDataTypes(ast)
        val expressions = mutableListOf<Visitable>()

        ast.accept(object : AstVisitor<Unit>() {
            override fun defaultVisit(obj: Any) {}
            override fun visit(assignmentStatement: AssignmentStatement) {
                expressions.add(assignmentStatement.expression)
            }
        })

        expressions
            .map {
                it.accept(ExpressionVisitor(State(), Scope()))
            }
            .zip(
                arrayOf(
                    VBool(AnyBit.BOOL, true),
                    VAnyInt(INT, -19),
                    VAnyInt(INT, 3),
                ),
            )
            .forEach { (a, b) -> Assertions.assertEquals(a, b) }
    }
}
