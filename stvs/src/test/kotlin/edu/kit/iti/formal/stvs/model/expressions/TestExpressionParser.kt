package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException
import org.junit.Assert
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
    private fun assertParseExpressionEqual(expr: String, expected: Expression?): Expression {
        val parsedExpr = parser.parseExpression(expr)
        println("$expr <means> $parsedExpr")
        Assert.assertEquals(
            expected,
            parsedExpr
        )
        return parsedExpr
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testConstants() {
        // TRUE means X = TRUE
        assertParseExpressionEqual(
            "TRUE",
            SimpleExpressions.equal(SimpleExpressions.`var`(columnName), SimpleExpressions.literal(true))
        )
        // both upper and lower case
        assertParseExpressionEqual(
            "false",
            SimpleExpressions.equal(SimpleExpressions.`var`(columnName), SimpleExpressions.literal(false))
        )
        // 1 means X = 1
        assertParseExpressionEqual(
            "1",
            SimpleExpressions.equal(SimpleExpressions.`var`(columnName), SimpleExpressions.literal(1))
        )
        // - means TRUE
        assertParseExpressionEqual("-", SimpleExpressions.literal(true))
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testVariables() {
        assertParseExpressionEqual(
            "b",
            SimpleExpressions.equal(SimpleExpressions.`var`(columnName), SimpleExpressions.`var`("b"))
        )
        assertParseExpressionEqual(
            "b = ! FALSE",
            SimpleExpressions.equal(
                SimpleExpressions.`var`("b"),
                SimpleExpressions.not(SimpleExpressions.literal(false))
            )
        )
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testVariablesWithIndex() {
        assertParseExpressionEqual(
            "A[-2]",
            SimpleExpressions.equal(SimpleExpressions.`var`(columnName), SimpleExpressions.`var`("A", -2))
        )
        assertParseExpressionEqual("(A[0])", SimpleExpressions.`var`("A", 0))
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
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testOnesided() {
        // < 2 means X < 2
        assertParseExpressionEqual(
            "< 2",
            SimpleExpressions.lessThan(SimpleExpressions.`var`(columnName), SimpleExpressions.literal(2))
        )
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testBinaryOperators() {
        val binaryOps: MutableMap<String, BinaryFunctionExpr.Op> = HashMap()
        binaryOps["+"] = BinaryFunctionExpr.Op.PLUS
        binaryOps[" - "] = BinaryFunctionExpr.Op.MINUS
        binaryOps["*"] = BinaryFunctionExpr.Op.MULTIPLICATION
        binaryOps["/"] = BinaryFunctionExpr.Op.DIVISION
        // power is commented out in grammar for some reason ?
        //binaryOps.put("**", BinaryFunctionExpr.Op.POWER);
        binaryOps["%"] = BinaryFunctionExpr.Op.MODULO
        binaryOps[" MOD "] = BinaryFunctionExpr.Op.MODULO

        binaryOps[">"] = BinaryFunctionExpr.Op.GREATER_THAN
        binaryOps["<"] = BinaryFunctionExpr.Op.LESS_THAN
        binaryOps[">="] = BinaryFunctionExpr.Op.GREATER_EQUALS
        binaryOps["<="] = BinaryFunctionExpr.Op.LESS_EQUALS

        binaryOps["="] = BinaryFunctionExpr.Op.EQUALS
        binaryOps["!="] = BinaryFunctionExpr.Op.NOT_EQUALS
        binaryOps["<>"] = BinaryFunctionExpr.Op.NOT_EQUALS

        binaryOps["&"] = BinaryFunctionExpr.Op.AND
        binaryOps[" AND "] = BinaryFunctionExpr.Op.AND
        binaryOps["|"] = BinaryFunctionExpr.Op.OR
        binaryOps[" OR "] = BinaryFunctionExpr.Op.OR
        binaryOps[" XOR "] = BinaryFunctionExpr.Op.XOR
        binaryOps[" xor "] = BinaryFunctionExpr.Op.XOR

        for ((operator, operation) in binaryOps) {
            assertParseExpressionEqual(
                "2" + operator + "2",
                BinaryFunctionExpr(operation, SimpleExpressions.literal(2), SimpleExpressions.literal(2))
            )
        }
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testUnaryOperators() {
        // parens enforce an "expression" rule (not single-sided or constant or blah)
        assertParseExpressionEqual("(- (2))", SimpleExpressions.negate(SimpleExpressions.literal(2)))
        assertParseExpressionEqual("(!TRUE)", SimpleExpressions.not(SimpleExpressions.literal(true)))
        assertParseExpressionEqual("(NOT TRUE)", SimpleExpressions.not(SimpleExpressions.literal(true)))
    }

    @Test

    fun testInvalidPlus() {
        assertFailsWith<SyntaxErrorReporter.ParserException> { parser.parseExpression("= +3") }
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testInterval() {
        // [1, 4] means X >= 1 AND X <= 4
        assertParseExpressionEqual(
            "[4, 1]",
            SimpleExpressions.and(
                SimpleExpressions.greaterEqual(
                    SimpleExpressions.`var`(columnName),
                    SimpleExpressions.literal(4)
                ), SimpleExpressions.lessEqual(SimpleExpressions.`var`(columnName), SimpleExpressions.literal(1))
            )
        )
    }

    @Test()
    fun testInvalidInterval() {
        assertFailsWith<ParseException> { parser.parseExpression("[1,3") }
    }

    @Test//(expected = UnsupportedExpressionException::class)
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testUnsupportedFunctioncall() {
        assertFailsWith<ParseException> { assertFailsWith<ParseException> { parser.parseExpression("function(1, 2)") } }
    }

    @Test//(expected = UnsupportedExpressionException::class)
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testUnsupportedGuardedIf() {
        assertFailsWith<ParseException> { assertFailsWith<ParseException> { parser.parseExpression("if :: TRUE -> FALSE :: FALSE -> TRUE fi") } }
    }

    @Test
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun testRecognizeEnum() {
        val colorsEnum = TypeEnum("COLORS", mutableListOf("red", "green", "blue"))
        val typeContext: MutableSet<Type> = HashSet()
        typeContext.add(colorsEnum)

        parser.setTypeContext(typeContext)
        assertParseExpressionEqual("(blue)", SimpleExpressions.literalEnum("blue", colorsEnum))
        //assertParseExpressionEqual("red", equal(var(cellName), literalEnum("red", colorsEnum)));
    }

    @Test//(expected = ParseException::class)
    @Throws(
        UnsupportedExpressionException::class, ParseException::class
    )
    fun testLongIntegerLiteral0() {
        assertFailsWith<ParseException> { assertFailsWith<ParseException> { parser.parseExpression("1324574839294857") } }
    }

    @Test//(expected = ParseException::class)
    @Throws(
        UnsupportedExpressionException::class, ParseException::class
    )
    fun testLongIntegerLiteral1() {
        assertFailsWith<ParseException> { parser.parseExpression("" + (Short.MAX_VALUE + 1)) }
    }

    @Test//(expected = ParseException::class)
    @Throws(
        UnsupportedExpressionException::class, ParseException::class
    )
    fun testLongIntegerLiteral2() {
        assertFailsWith<ParseException> { parser.parseExpression("" + (Short.MIN_VALUE - 1)) }
    }
}
