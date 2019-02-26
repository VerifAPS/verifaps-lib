package edu.kit.iti.formal.automation.il

import LoadHelp
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.IEC61131Facade.InstructionList.parseBody
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.util.CodeWriter
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import java.io.StringWriter
import java.nio.file.Files

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.02.19)
 */
class FirstIlBodyTest {
    @Test
    fun lexfirst() {
        val url = LoadHelp.getResource(
                "edu/kit/iti/formal/automation/il/p180_iec61131.il")
        Assumptions.assumeTrue(url != null)
        val lexer = IEC61131Lexer(CharStreams.fromPath(url))
        lexer.pushMode(1)
        val tokens = lexer.allTokens
        tokens.forEach { println("$it; type: ${lexer.vocabulary.getDisplayName(it.type)}") }
        Assertions.assertTrue(tokens.all { it.type != IEC61131Lexer.ERROR_CHAR })
    }

    @Test
    fun first() {
        val url = LoadHelp.getResource(
                "edu/kit/iti/formal/automation/il/p180_iec61131.il")
        Assumptions.assumeTrue(url != null)
        val lexer = IEC61131Lexer(CharStreams.fromPath(url))
        lexer.pushMode(1)
        val parser = IEC61131Parser(CommonTokenStream(lexer))
        val ctx = parser.ilBody()
        println(ctx.toStringTree(parser))
    }

    @Test
    fun testFacade() {
        val url = LoadHelp.getResource(
                "edu/kit/iti/formal/automation/il/p180_iec61131.il")
        Assumptions.assumeTrue(url != null)
        Files.newBufferedReader(url).use {
            val input = it.readText()
            val body = IEC61131Facade.InstructionList.parseBody(input)
            val sw = StringWriter()
            body.accept(IlPrinter(CodeWriter(sw)))
            println(sw)
        }
    }

    @Test
    fun testTranslate(): Unit {
        val url = LoadHelp.getResource(
                "edu/kit/iti/formal/automation/il/p180_iec61131.il")
        Assumptions.assumeTrue(url != null)
        Files.newBufferedReader(url).use {
            val input = it.readText()
            val body = IEC61131Facade.InstructionList.parseBody(input)
            val (scope, stCode) = Il2St(body).call()
            println(IEC61131Facade.print(stCode))
        }
    }

    @Test
    fun testTranslateJmp(): Unit {
        val ilBody = parseBody("""LD 5
            ST A
            EQ B
            JMPC next
            LD A
            ADD B
            ST A
            next :
            ST X
        """.trimIndent())
        val (scope, stCode) = Il2St(ilBody).call()
        println(IEC61131Facade.print(stCode))
    }
}