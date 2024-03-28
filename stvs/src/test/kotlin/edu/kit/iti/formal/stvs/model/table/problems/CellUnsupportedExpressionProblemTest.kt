package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class CellUnsupportedExpressionProblemTest {
    private var problem: CellUnsupportedExpressionProblem? = null
    private var unsupportedExpressionEx: UnsupportedExpressionException? = null

    @BeforeEach
    @Throws(Exception::class)
    fun setUp() {
        unsupportedExpressionEx = UnsupportedExpressionException("ExpressionText")
        problem = CellUnsupportedExpressionProblem(unsupportedExpressionEx!!, "A", 4)
    }

    @Test
    fun unsupportedExpression() {
        Assertions.assertEquals(unsupportedExpressionEx, problem!!.unsupportedExpression)
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!, "A", 4
        )
        Assertions.assertEquals(identical, problem)
        Assertions.assertNotEquals(null, problem)
        Assertions.assertEquals(problem, problem)
        val notIdentical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!, "A", 5
        )
        Assertions.assertNotEquals(notIdentical, problem)
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        val identical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!, "A", 4
        )
        Assertions.assertEquals(identical.hashCode().toLong(), problem.hashCode().toLong())
        Assertions.assertEquals(problem.hashCode().toLong(), problem.hashCode().toLong())
        val notIdentical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!, "A", 5
        )
        Assertions.assertNotEquals(notIdentical.hashCode().toLong(), problem.hashCode().toLong())
    }
}
