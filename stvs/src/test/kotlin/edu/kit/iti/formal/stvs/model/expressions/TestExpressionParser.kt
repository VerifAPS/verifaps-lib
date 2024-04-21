package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.equal
import edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.lessThan
import edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.literal
import edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.variable
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by philipp on 17.01.17.
 */
class TestExpressionParser {
    // Initialize parser with context information:
    private val columnName = "X"
    private val parser = ExpressionParser(columnName)

    @Throws(ParseException::class, UnsupportedExpressionException::class)
    private fun assertParseExpressionEqual(expr: String, expected: Expression): Expression {
        val parsedExpr = parser.parseExpression(expr)
        println("$expr <means> $parsedExpr")
        assertEquals(expected, parsedExpr)
        return parsedExpr
    }

    @Test
    fun testConstants() {
        // TRUE means X = TRUE
        assertParseExpressionEqual("TRUE", equal(variable(columnName), literal(true)))
        // both upper and lower case
        assertParseExpressionEqual("false", equal(variable(columnName), literal(false)))
        // 1 means X = 1
        assertParseExpressionEqual("1", equal(variable(columnName), literal(1)))
        // - means TRUE
        assertParseExpressionEqual("-", literal(true))
    }

    @Test
    fun testVariables() {
        assertParseExpressionEqual("b", equal(variable(columnName), variable("b")))
        assertParseExpressionEqual(
            "b = ! FALSE",
            equal(variable("b"), SimpleExpressions.not(literal(false)))
        )
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testVariablesWithIndex() {
        assertParseExpressionEqual("A[-2]", equal(variable(columnName), variable("A", -2)))
        assertParseExpressionEqual("(A[0])", variable("A", 0))
    }

    @Test
    fun testVariablesOnlyNegativeIndex1() {
        assertFailsWith<UnsupportedExpressionException> { parser.parseExpression("A[2]") }
    }

    @Test
    fun testVariablesOnlyNegativeIndex2() {
        assertFailsWith<UnsupportedExpressionException> { parser.parseExpression("(A[2])") }
    }

    @Test
    fun testOnesided() {
        // < 2 means X < 2
        assertParseExpressionEqual("< 2", lessThan(variable(columnName), literal(2)))
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testBinaryOperators() {
        val binaryOps = hashMapOf(
            "+" to BinaryFunctionExpr.Op.PLUS,
            " - " to BinaryFunctionExpr.Op.MINUS,
            "*" to BinaryFunctionExpr.Op.MULTIPLICATION,
            "/" to BinaryFunctionExpr.Op.DIVISION,
            // power is commented out in grammar for some reason ?
            //binaryOps.put("**", BinaryFunctionExpr.Op.POWER);
            "%" to BinaryFunctionExpr.Op.MODULO,
            " MOD " to BinaryFunctionExpr.Op.MODULO,
            ">" to BinaryFunctionExpr.Op.GREATER_THAN,
            "<" to BinaryFunctionExpr.Op.LESS_THAN,
            ">=" to BinaryFunctionExpr.Op.GREATER_EQUALS,
            "<=" to BinaryFunctionExpr.Op.LESS_EQUALS,
            "=" to BinaryFunctionExpr.Op.EQUALS,
            "!=" to BinaryFunctionExpr.Op.NOT_EQUALS,
            "<>" to BinaryFunctionExpr.Op.NOT_EQUALS,
            "&" to BinaryFunctionExpr.Op.AND,
            " AND " to BinaryFunctionExpr.Op.AND,
            "|" to BinaryFunctionExpr.Op.OR,
            " OR " to BinaryFunctionExpr.Op.OR,
            " XOR " to BinaryFunctionExpr.Op.XOR,
            " xor " to BinaryFunctionExpr.Op.XOR
        )

        for ((operator, operation) in binaryOps) {
            assertParseExpressionEqual(
                "2" + operator + "2",
                BinaryFunctionExpr(operation, literal(2), literal(2))
            )
        }
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testUnaryOperators() {
        // parens enforce an "expression" rule (not single-sided or constant or blah)
        assertParseExpressionEqual("(- (2))", SimpleExpressions.negate(literal(2)))
        assertParseExpressionEqual("(!TRUE)", SimpleExpressions.not(literal(true)))
        assertParseExpressionEqual("(NOT TRUE)", SimpleExpressions.not(literal(true)))
    }

    @Test
    fun testInvalidPlus() {
        assertFailsWith<ParseException> { parser.parseExpression("= +3") }
    }

    @Test
    fun testInterval() {
        // [1, 4] means X >= 1 AND X <= 4
        assertParseExpressionEqual(
            "[4, 1]",
            SimpleExpressions.and(
                SimpleExpressions.lessEqual(
                    literal(4), variable(columnName)
                ), SimpleExpressions.lessEqual(variable(columnName), literal(1))
            )
        )
    }

    @Test()
    fun testInvalidInterval() {
        assertFailsWith<ParseException> { parser.parseExpression("[1,3") }
    }

    @Test
    fun testUnsupportedFunctioncall() {
        assertFailsWith<UnsupportedExpressionException> {
            parser.parseExpression("function(1, 2)")
        }
    }

    @Test
    fun testUnsupportedGuardedIf() {
        parser.parseExpression("if :: TRUE -> FALSE :: FALSE -> TRUE fi")
    }

    @Test
    fun testRecognizeEnum() {
        val colorsEnum = TypeEnum("COLORS", mutableListOf("red", "green", "blue"))
        val typeContext: MutableSet<Type> = HashSet()
        typeContext.add(colorsEnum)

        parser.setTypeContext(typeContext)
        assertParseExpressionEqual("(blue)", SimpleExpressions.literalEnum("blue", colorsEnum))
        //assertParseExpressionEqual("red", equal(var(cellName), literalEnum("red", colorsEnum)));
    }

    @Test
    fun testLongIntegerLiteral0() {
        assertFailsWith<NumberFormatException> { parser.parseExpression("1324574839294857") }
    }

    @Test
    fun testLongIntegerLiteral1() {
        parser.parseExpression("" + (Short.MAX_VALUE + 1))
    }

    @Test
    fun testLongIntegerLiteral2() {
        parser.parseExpression("" + (Short.MIN_VALUE - 1))
    }
}
