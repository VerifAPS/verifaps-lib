package edu.kit.iti.formal.automation

import org.antlr.v4.runtime.CharStreams
import org.junit.Assert
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.IOException

/**
 * Created by weigl on 02.08.16.
 */
@RunWith(Parameterized::class)
class ValidExpressionTest(val validExpression: String) {

    @Test
    fun testValidExpression() {
        assertTrue(test(validExpression))
    }

    @Test
    fun testCopy() {
        val e = IEC61131Facade.expr(this.validExpression)
        Assert.assertEquals(e, e.clone())
    }

    companion object {

        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        @Throws(IOException::class)
        fun setup(): Iterable<Array<Any>> {
            return TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/valid.txt")
        }

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
}
