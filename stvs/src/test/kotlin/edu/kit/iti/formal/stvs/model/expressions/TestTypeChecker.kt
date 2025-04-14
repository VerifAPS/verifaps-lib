package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

class TestTypeChecker {
    private val varTypeCtx = mapOf("X" to TypeInt)
    private val checker = TypeChecker(varTypeCtx)


    @Test
    @Throws(TypeCheckException::class)
    fun testValidType() {
        // Colors = Red, Blue
        // Red == Blue && X == 3 && 5 + X == 8 && TRUE

        val colorsEnum = enumOfName("Colors", "Red", "Blue")

        val redEqualsBlue =
            SimpleExpressions.equal(
                SimpleExpressions.literal(colorsEnum.valueOf("Red")),
                SimpleExpressions.literal(colorsEnum.valueOf("Blue"))
            )

        val xEqualsThree =
            SimpleExpressions.equal(
                SimpleExpressions.variable("X"),
                SimpleExpressions.literal(3)
            )

        val sumIsEleven =
            SimpleExpressions.equal(
                SimpleExpressions.plus(SimpleExpressions.literal(5), SimpleExpressions.variable("X")),
                SimpleExpressions.literal(8)
            )

        val trueExpr = SimpleExpressions.literal(true)

        val validExpression =
            SimpleExpressions.and(
                redEqualsBlue,
                SimpleExpressions.and(xEqualsThree, SimpleExpressions.and(sumIsEleven, trueExpr))
            )

        val type = checker.typeCheck(validExpression)
        Assertions.assertEquals(type, TypeBool)
    }

    @Test//(expected = TypeCheckException::class)
    @Throws(TypeCheckException::class)
    fun testInvalidArgumentType() {
        val invalidExpression =
            SimpleExpressions.and(SimpleExpressions.literal(false), SimpleExpressions.literal(2))
        assertFailsWith<TypeCheckException> {
            checker.typeCheck(invalidExpression)
        }
    }
}
