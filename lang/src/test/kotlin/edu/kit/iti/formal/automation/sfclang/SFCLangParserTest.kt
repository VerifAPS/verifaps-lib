package edu.kit.iti.formal.automation.sfclang

import LoadHelp
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.PrettyPrinterTest
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.nio.file.Path

/**
 * Created by weigl on 07.02.16.
 */
object SFCLangParserTest {

    @ParameterizedTest
    @MethodSource("getSfcs")
    fun read(inputFilename: Path) {
        val (parser, ctx) = parseSfc(inputFilename)
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
        Assertions.assertFalse(parser.errorReporter.hasErrors())
        Assertions.assertNotNull(ctx.sfcBody)
    }

    private fun parseSfc(inputFilename: Path): Pair<IEC61131Parser, FunctionBlockDeclaration> {
        val parser = IEC61131Facade.getParser(CharStreams.fromPath(inputFilename))
        val ctx = parser.function_block_declaration().accept(IECParseTreeToAST()) as FunctionBlockDeclaration
        return Pair(parser, ctx)
    }

    @ParameterizedTest
    @MethodSource("getSfcs")
    @Disabled
    fun prettyPrintByString(input: Path) {
        val (_, ctx) = parseSfc(input)
        PrettyPrinterTest.testPrettyPrintByString(ctx, input)
    }


    @JvmStatic
    fun getSfcs() = LoadHelp.getResources("/edu/kit/iti/formal/automation/sfclang/data")
}
