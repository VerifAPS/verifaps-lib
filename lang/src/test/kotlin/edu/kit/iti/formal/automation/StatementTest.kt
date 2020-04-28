package edu.kit.iti.formal.automation


import LoadHelp
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.nio.file.Path

object StatementTest {
    @ParameterizedTest(name = "testParser: {0}")
    @MethodSource("getStatements")
    fun testParser(testFile: Path) {
        val parser = IEC61131Facade.getParser(CharStreams.fromPath(testFile))
        val ctx = parser.statement_list()
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
    }

    @ParameterizedTest(name = "copy: {0}")
    @MethodSource("getStatements")
    fun testCopy(testFile: Path) {
        println("F:$testFile")
        val sl = IEC61131Facade.statements(CharStreams.fromPath(testFile))
        Assertions.assertEquals(sl, sl.setAllMetadata())
    }

    @JvmStatic
    fun getStatements() = LoadHelp.getStatements()
}
