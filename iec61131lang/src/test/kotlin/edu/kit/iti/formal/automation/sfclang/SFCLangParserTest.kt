package edu.kit.iti.formal.automation.sfclang

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.PrettyPrinterTest
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import java.io.File

/**
 * Created by weigl on 07.02.16.
 */
class SFCLangParserTest() {

    @ParameterizedTest
    @SFCSource
    fun read(inputFilename: String) {
        val (parser, ctx) = parseSfc(inputFilename)
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
        Assertions.assertFalse(parser.errorReporter.hasErrors())
        Assertions.assertNotNull(ctx.sfcBody)
    }

    private fun parseSfc(inputFilename: String): Pair<IEC61131Parser, FunctionBlockDeclaration> {
        val parser = IEC61131Facade.getParser(CharStreams.fromStream(javaClass.getResourceAsStream(inputFilename)))
        val ctx = parser.function_block_declaration().accept(IECParseTreeToAST()) as FunctionBlockDeclaration
        return Pair(parser, ctx)
    }

    @ParameterizedTest
    @SFCSource
    @Disabled
    fun prettyPrintByString(inputFilename: String) {
        val (_, ctx) = parseSfc(inputFilename)
        PrettyPrinterTest.testPrettyPrintByString(ctx,
                File("src/test/resources/edu/kit/iti/formal/automation/sfclang/", inputFilename))
    }


}

@ValueSource(strings = ["data/Algo1_left.sfc", "data/Algo1_right.sfc", "data/Delay1_left.sfc", "data/Delay1_right.sfc", "data/EmptyStep1_left.sfc", "data/EmptyStep1_right.sfc", "data/Idempotence1_left.sfc", "data/Idempotence1_right.sfc", "data/Input1_left.sfc", "data/Input1_right.sfc", "data/LoopUnwinding1_left.sfc", "data/LoopUnwinding1_right.sfc", "data/Transition1_left.sfc", "data/Transition1_right.sfc", "data/Transition2_left.sfc", "data/Transition2_right.sfc", "data/Types1_left.sfc", "data/Types1_right.sfc"])
annotation class SFCSource
