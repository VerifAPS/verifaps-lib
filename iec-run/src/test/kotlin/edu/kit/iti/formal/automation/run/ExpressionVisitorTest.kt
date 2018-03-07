package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable
import org.junit.Test
import java.math.BigInteger
import kotlin.test.assertEquals

class ExpressionVisitorTest {
    @Test
    fun basicTest() {
        val ast = getAst(this.javaClass.getResource("expressionVisitorTest.basicTest.st"))
        val expressions = mutableListOf<Visitable>();

/*-
 * #%L
 * iec-run
 * %%
 * Copyright (C) 2018 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */
        ast.accept<AnyDt>(object: DefaultVisitor<Unit>() {
            override fun defaultVisit(visitable: Visitable?) {
            }

            override fun visit(programDeclaration: ProgramDeclaration?) {
                return programDeclaration!!.stBody.accept(this)
            }

            override fun visit(statements: StatementList?) {
                statements!!.forEach { it.accept<AnyDt>(this) }
            }

            override fun visit(assignmentStatement: AssignmentStatement?) {
                expressions.add(assignmentStatement!!.expression)
            }
        })

        val expressionValues: List<ExpressionValue> = expressions.map {
            it.accept<ExpressionValue>(ExpressionVisitor(TopState(), Scope())) as ExpressionValue
        }

        println(expressionValues.map { it.toString() }.joinToString("\n"))
        assertEquals(arrayListOf(
                Values.VBool(AnyBit.BOOL, true),
                Values.VAnyInt(DataTypes.UNKNWON_SIGNED_INT, BigInteger.valueOf(-19)),
                Values.VAnyInt(DataTypes.USINT, BigInteger.valueOf(3))
        ).toString(),
        expressionValues.toString())
    }
}
