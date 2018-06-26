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
import org.junit.Assert
import org.junit.Test

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
                .zip(arrayOf(VBool(AnyBit.BOOL, true),
                        VAnyInt(INT, -19),
                        VAnyInt(INT, 3)))
                .forEach { (a, b) -> Assert.assertEquals(a, b) }
    }
}
