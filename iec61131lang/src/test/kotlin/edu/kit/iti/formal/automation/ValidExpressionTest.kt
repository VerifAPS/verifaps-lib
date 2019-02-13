package edu.kit.iti.formal.automation

import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * Created by weigl on 02.08.16.
 */
object ValidExpressionTest {
    fun testValidExpression(validExpression: String) {
        assertTrue(test(validExpression))
    }

    fun testCopy(validExpression: String) {
        val e = IEC61131Facade.expr(validExpression)
        Assertions.assertEquals(e, e.clone())
    }


    @TestFactory
    fun setupValidExpression(): List<DynamicTest> =
            TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/valid.txt")
                    .map { DynamicTest.dynamicTest(it) { testValidExpression(it) } }


    @TestFactory
    fun setupCopyExpression(): List<DynamicTest> =
            TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/valid.txt")
                    .map { DynamicTest.dynamicTest(it) { testCopy(it) } }

    internal fun test(s: String?): Boolean {
        val parser = IEC61131Facade.getParser(CharStreams.fromString(s!!))
        try {
            val ctx = parser.expression()
            println(ctx.toString(parser))
            assertEquals("input was not completely consumed",
                    "<EOF>", ctx.stop.tokenSource.nextToken().text)
        } catch (e: Exception) {
            e.printStackTrace()
            return false
        }

        return parser.numberOfSyntaxErrors == 0
    }
}
