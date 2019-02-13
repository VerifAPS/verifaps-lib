package edu.kit.iti.formal.automation


import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * @author Alexander Weigl
 * @version 1 (02.08.16)
 */
object InValidExpressionTest {
    private fun testInValidExpression(invalid: String) {
        val parser = IEC61131Facade.getParser(CharStreams.fromString(invalid))
        var error = try {
            val ctx = parser.expression()
            println(ctx.toString(parser))
            println(IEC61131Facade.print(IEC61131Facade.expr(invalid)))
            println(ctx.stop.tokenSource.nextToken())
            ctx.stop.tokenSource.nextToken().text != "EOF"
            //error = false;
        } catch (e: Exception) {
            true
        }

        error = error || parser.numberOfSyntaxErrors > 0
        println(parser.numberOfSyntaxErrors)
        assertTrue(error)
    }

    @TestFactory
    fun setup(): Iterable<DynamicTest> =
            TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/invalid.txt")
                    .map { DynamicTest.dynamicTest(it) { testInValidExpression(it) } }
}

