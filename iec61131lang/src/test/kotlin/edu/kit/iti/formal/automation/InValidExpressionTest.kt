package edu.kit.iti.formal.automation


import org.antlr.v4.runtime.CharStreams
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (02.08.16)
 */
@RunWith(Parameterized::class)
class InValidExpressionTest(var invalid: String) {
    @Test
    fun testInValidExpression() {
        val parser = IEC61131Facade.getParser(CharStreams.fromString(invalid))
        var error = false
        try {
            val ctx = parser.expression()
            println(ctx.toString(parser))
            println(IEC61131Facade.print(IEC61131Facade.expr(invalid)))
            println(ctx.stop.tokenSource.nextToken())
            error = ctx.stop.tokenSource.nextToken().text != "EOF"
            //error = false;
        } catch (e: Exception) {
            error = true
        }

        error = error || parser.numberOfSyntaxErrors > 0
        println(parser.numberOfSyntaxErrors)
        assertTrue(error)
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        @Throws(IOException::class)
        fun setup(): Iterable<Array<Any>> {
            return TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/invalid.txt")
        }
    }
}

