package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import org.antlr.v4.runtime.ANTLRFileStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.IOException
import java.util.*


@RunWith(Parameterized::class)
class TypesTest(val testFile: String) {
    @Test
    @Throws(IOException::class)
    fun testParser() {
        val lexer = IEC61131Lexer(ANTLRFileStream(testFile))
        val parser = IEC61131Parser(CommonTokenStream(lexer))
        parser.data_type_declaration()
        Assert.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
    }

    @Test
    @Throws(IOException::class)
    fun testCopy() {
        val ast = IEC61131Facade.file(CharStreams.fromFileName(testFile))
        Assert.assertEquals(ast, ast.clone())
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun get(): ArrayList<Array<Any>> {
            val resources = ProgramTest.getResources("edu/kit/iti/formal/automation/st/types")
            val list = ArrayList<Array<Any>>()
            for (f in resources!!) {
                list.add(arrayOf(f.absolutePath))
            }
            return list
        }
    }
}
