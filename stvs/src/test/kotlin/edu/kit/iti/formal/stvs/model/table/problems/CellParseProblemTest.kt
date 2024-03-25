package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.table.ConstraintCell
import org.hamcrest.CoreMatchers
import org.hamcrest.MatcherAssert
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.*

/**
 * Created by bal on 26.02.17.
 */
class CellParseProblemTest {
    private var problem: CellParseProblem? = null
    private var parseEx: ParseException? = null

    @BeforeEach
    fun setUp() {
        parseEx =
            ParseException(1, 2, "extraneous input '<>' expecting {'(', '-', NOT, 'if', T, F, IDENTIFIER, INTEGER}")
        problem = CellParseProblem(parseEx!!, "A", 4)
    }

    @Test
    @Throws(Exception::class)
    fun expressionOrProblemForCell() {
        val typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL)
        val typeMap: MutableMap<String, Type> = HashMap()
        typeMap["A"] = TypeInt.INT
        typeMap["B"] = TypeBool.BOOL
        val typeChecker = TypeChecker(typeMap)
        val problematicCell = ConstraintCell("3<<>4")
        try {
            ConstraintSpecificationValidator.tryValidateCellExpression(
                typeContext, typeChecker, "A", 4,
                problematicCell
            )
        } catch (problem: CellProblem) {
            MatcherAssert.assertThat(
                problem, CoreMatchers.instanceOf(
                    CellParseProblem::class.java
                )
            )
            Assertions.assertEquals(this.problem, problem)
        }
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical = CellParseProblem(parseEx!!, "A", 4)
        Assertions.assertEquals(problem, identical)
        Assertions.assertNotEquals(problem, null)
        Assertions.assertEquals(problem, problem)
        Assertions.assertNotEquals(CellParseProblem(parseEx!!, "B", 4), problem)
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        val identical = CellParseProblem(parseEx!!, "A", 4)
        Assertions.assertEquals(problem.hashCode().toLong(), identical.hashCode().toLong())
        Assertions.assertEquals(problem.hashCode().toLong(), problem.hashCode().toLong())
        Assertions.assertNotEquals(CellParseProblem(parseEx!!, "B", 4).hashCode().toLong(), problem.hashCode().toLong())
    }

    @Test
    fun parseException() {
        Assertions.assertEquals(parseEx, problem!!.parseException)
    }
}
