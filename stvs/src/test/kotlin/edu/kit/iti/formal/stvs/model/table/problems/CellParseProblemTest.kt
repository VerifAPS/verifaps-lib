package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.table.ConstraintCell
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by bal on 26.02.17.
 */
class CellParseProblemTest {
    private var parseEx =
        ParseException(1, 2, "extraneous input '<>' expecting {'(', '-', NOT, 'if', T, F, IDENTIFIER, INTEGER}")
    private var problem = CellParseProblem(parseEx, "A", 4)


    @Test
    fun expressionOrProblemForCell() {
        val typeContext = listOf(TypeInt.INT, TypeBool.BOOL)
        val typeMap: MutableMap<String, Type> = HashMap()
        typeMap["A"] = TypeInt.INT
        typeMap["B"] = TypeBool.BOOL
        val typeChecker = TypeChecker(typeMap)
        val problematicCell = ConstraintCell("3<<>4")
        assertFailsWith<CellParseProblem> {
            ConstraintSpecificationValidator.tryValidateCellExpression(
                typeContext, typeChecker, "A", 4,
                problematicCell
            )
        }
    }

    @Test
    fun testEquals() {
        val identical = CellParseProblem(parseEx, "A", 4)
        Assertions.assertEquals(problem, identical)
        Assertions.assertNotEquals(problem, null)
        Assertions.assertEquals(problem, problem)
        Assertions.assertNotEquals(CellParseProblem(parseEx, "B", 4), problem)
    }

    @Test
    fun testHashCode() {
        val identical = CellParseProblem(parseEx, "A", 4)
        Assertions.assertEquals(problem.hashCode().toLong(), identical.hashCode().toLong())
        Assertions.assertEquals(problem.hashCode().toLong(), problem.hashCode().toLong())
        Assertions.assertNotEquals(CellParseProblem(parseEx, "B", 4).hashCode().toLong(), problem.hashCode().toLong())
    }

    @Test
    fun parseException() {
        Assertions.assertEquals(parseEx, problem.parseException)
    }
}
