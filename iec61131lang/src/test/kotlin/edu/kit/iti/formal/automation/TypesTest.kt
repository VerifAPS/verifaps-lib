package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import org.antlr.v4.runtime.ANTLRFileStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.util.*

class TypesTest {
    @ParameterizedTest
    @MethodSource("getTypeTests")
    fun testParser(testFile: String) {
        val lexer = IEC61131Lexer(ANTLRFileStream(testFile))
        val parser = IEC61131Parser(CommonTokenStream(lexer))
        parser.data_type_declaration()
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
    }

    @ParameterizedTest
    @MethodSource("getTypeTests")
    fun testCopy(testFile: String) {
        val ast = IEC61131Facade.file(CharStreams.fromFileName(testFile))
        Assertions.assertEquals(ast, ast.clone())
    }

    companion object {
        @JvmStatic
        fun getTypeTests(): ArrayList<Array<Any>> {
            val resources = ProgramTest.getResources("edu/kit/iti/formal/automation/st/types")
            val list = ArrayList<Array<Any>>()
            for (f in resources!!) {
                list.add(arrayOf(f.absolutePath))
            }
            return list
        }
    }
}
