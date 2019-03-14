package edu.kit.iti.formal.automation

import LoadHelp
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.nio.file.Path

object TypesTest {
    @ParameterizedTest
    @MethodSource("getTypeTests")
    fun testParser(testFile: Path) {
        val parser = IEC61131Facade.getParser(CharStreams.fromPath(testFile))
        parser.data_type_declaration()
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
    }

    @ParameterizedTest
    @MethodSource("getTypeTests")
    fun testCopy(testFile: Path) {
        val ast = IEC61131Facade.file(testFile)
        Assertions.assertEquals(ast, ast.clone())
    }

    @JvmStatic
    fun getTypeTests() = LoadHelp.getTypes()
}
