package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.scope.LocalScope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable
import org.junit.Test
import java.math.BigInteger
import kotlin.test.assertEquals

class ExpressionVisitorTest {
    @Test
    fun basicTest() {
        val ast = getAst(this.javaClass.getResource("expressionVisitorTest.testIfStatement.st"))
        val expressions = ArrayList<Expression>()
        ast.accept<Any>(object: DefaultVisitor<Unit>() {
            override fun defaultVisit(visitable: Visitable?) {
            }

            override fun visit(programDeclaration: ProgramDeclaration?) {
                return programDeclaration!!.programBody.accept(this)
            }

            override fun visit(statements: StatementList?) {
                statements!!.forEach { it.accept<Any>(this) }
            }

            override fun visit(assignmentStatement: AssignmentStatement?) {
                expressions.add(assignmentStatement!!.expression)
            }
        })

        val expressionValues: List<ExpressionValue> = expressions.map {
            it.accept<ExpressionValue>(ExpressionVisitor(TopState(), LocalScope())) as ExpressionValue
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