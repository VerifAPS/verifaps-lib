package edu.kit.iti.formal.automation

import TestUtils
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

/**
 * Created by weigl on 02.08.16.
 */
object ValidExpressionTest {
    @ParameterizedTest(name = "{0}")
    @MethodSource("getExpressions")
    fun testValidExpression(validExpression: String) {
        assertTrue(test(validExpression))
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("getExpressions")
    fun testCopy(validExpression: String) {
        val e = IEC61131Facade.expr(validExpression)
        Assertions.assertEquals(e, e.clone())
    }


    @JvmStatic
    fun getExpressions() = TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/valid.txt")

    internal fun test(s: String?): Boolean {
        val parser = IEC61131Facade.getParser(CharStreams.fromString(s!!))
        try {
            val ctx = parser.expression()
            println(ctx.toString(parser))
            assertEquals("<EOF>", ctx.stop.tokenSource.nextToken().text,
                    "input was not completely consumed")
        } catch (e: Exception) {
            e.printStackTrace()
            return false
        }

        return parser.numberOfSyntaxErrors == 0
    }
}
