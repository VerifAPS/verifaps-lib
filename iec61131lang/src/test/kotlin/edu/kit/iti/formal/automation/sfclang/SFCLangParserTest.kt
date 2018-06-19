package edu.kit.iti.formal.automation.sfclang

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.PrettyPrinterTest
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import org.antlr.v4.runtime.CharStreams
import org.junit.Assert
import org.junit.Assume
import org.junit.Before
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File
import java.io.IOException
import java.util.*

/**
 * Created by weigl on 07.02.16.
 */
@RunWith(Parameterized::class)
class SFCLangParserTest(private val inputFilename: String) {
    private var ctx: FunctionBlockDeclaration? = null
    private var parser: IEC61131Parser? = null

    @Before
    @Throws(IOException::class)
    fun parse() {
        parser = IEC61131Facade.getParser(CharStreams.fromStream(javaClass.getResourceAsStream(inputFilename)))
        ctx = parser!!.function_block_declaration().accept(IECParseTreeToAST()) as FunctionBlockDeclaration
    }

    @Test
    @Throws(ClassNotFoundException::class, IOException::class)
    fun read() {
        Assert.assertEquals(0, parser!!.numberOfSyntaxErrors.toLong())
        Assert.assertFalse(parser!!.errorReporter.hasErrors())
        Assert.assertNotNull(ctx!!.sfcBody)
    }

    @Test
    @Throws(IOException::class)
    fun prettyPrintByString() {
        Assume.assumeTrue(false)
        PrettyPrinterTest.testPrettyPrintByString(ctx!!,
                File("src/test/resources/edu/kit/iti/formal/automation/sfclang/", inputFilename))
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun data(): Collection<String> {
            return Arrays.asList("data/Algo1_left.sfc",
                    "data/Algo1_right.sfc",
                    "data/Delay1_left.sfc",
                    "data/Delay1_right.sfc",
                    "data/EmptyStep1_left.sfc",
                    "data/EmptyStep1_right.sfc",
                    "data/Idempotence1_left.sfc",
                    "data/Idempotence1_right.sfc",
                    "data/Input1_left.sfc",
                    "data/Input1_right.sfc",
                    "data/LoopUnwinding1_left.sfc",
                    "data/LoopUnwinding1_right.sfc",
                    "data/Transition1_left.sfc",
                    "data/Transition1_right.sfc",
                    "data/Transition2_left.sfc",
                    "data/Transition2_right.sfc",
                    "data/Types1_left.sfc",
                    "data/Types1_right.sfc")
        }
    }
}
