package edu.kit.iti.formal.automation


import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.io.File
import java.util.*

class StatementTest {
    @ParameterizedTest
    @MethodSource("getStatments")
    fun testParser(testFile: String) {
        val parser = IEC61131Facade.getParser(CharStreams.fromFileName(testFile))
        val ctx = parser.statement_list()
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
    }

    @ParameterizedTest
    @MethodSource("getStatments")
    fun testCopy(testFile: String) {
        val sl = IEC61131Facade.statements(CharStreams.fromFileName(testFile))
        Assertions.assertEquals(sl, sl.clone())
    }

    companion object {
        @JvmStatic
        fun getStatements(): Iterable<Array<Any>> {
            val resources = ProgramTest.getResources("edu/kit/iti/formal/automation/st/statements")
            val list = ArrayList<Array<Any>>()
            for (f in resources!!) {
                list.add(arrayOf(f.absolutePath))
            }
            return list
        }
    }
}
