package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.problems.CellTypeProblem.Companion.tryTypeCheckCellExpression
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class CellTypeProblemTest {
    private var typeCheckEx: TypeCheckException? = null
    private var problem: CellTypeProblem? = null

    @BeforeEach
    fun setUp() {
        typeCheckEx = TypeCheckException(
            BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, LiteralExpr(ValueInt(2)), LiteralExpr(ValueBool.TRUE)),
            "Expected type \"BOOL\","
                    + "but got \"INT\""
        )
        problem = CellTypeProblem(typeCheckEx!!, "A", 4)
    }

    @Test
    @Throws(Exception::class)
    fun tryTypeCheckCellExpression() {
        val typeMap = mapOf("A" to TypeInt, "B" to TypeBool)
        val typeChecker = TypeChecker(typeMap)
        val problematicCell = SimpleExpressions.and(SimpleExpressions.literal(2), SimpleExpressions.literal(true))
        try {
            tryTypeCheckCellExpression(
                typeChecker, "A", 4, problematicCell
            )
        } catch (exc: SpecProblemException) {
            Assertions.assertEquals(problem, exc.problem)
        }
    }

    @Test
    fun typeCheckException() {
        Assertions.assertEquals(typeCheckEx, problem!!.exception)
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical = CellTypeProblem(typeCheckEx!!, "A", 4)
        Assertions.assertEquals(problem, identical)
        Assertions.assertNotEquals(problem, null)
        Assertions.assertEquals(problem, problem)
        val notIdentical = CellTypeProblem(typeCheckEx!!, "A", 5)
        Assertions.assertNotEquals(notIdentical, problem)
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        val identical = CellTypeProblem(typeCheckEx!!, "A", 4)
        Assertions.assertEquals(problem.hashCode().toLong(), identical.hashCode().toLong())
        Assertions.assertEquals(problem.hashCode().toLong(), problem.hashCode().toLong())
        val notIdentical = CellTypeProblem(typeCheckEx!!, "A", 5)
        Assertions.assertNotEquals(notIdentical.hashCode().toLong(), problem.hashCode().toLong())
    }
}
