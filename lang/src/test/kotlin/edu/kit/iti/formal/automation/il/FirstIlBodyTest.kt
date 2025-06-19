/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 *
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
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
        val url = LoadHelp.getResource("edu/kit/iti/formal/automation/il/p180_iec61131.il")
        Assumptions.assumeTrue(url != null)
        val lexer = IEC61131Lexer(CharStreams.fromPath(url))
        lexer.pushMode(1)
        val tokens = lexer.allTokens
        tokens.forEach { println("$it; type: ${lexer.vocabulary.getDisplayName(it.type)}") }
        Assertions.assertTrue(tokens.all { it.type != IEC61131Lexer.ERROR_CHAR })
    }

    @Test
    fun first() {
        val url = LoadHelp.getResource("edu/kit/iti/formal/automation/il/p180_iec61131.il")
        Assumptions.assumeTrue(url != null)
        val lexer = IEC61131Lexer(CharStreams.fromPath(url))
        lexer.pushMode(1)
        val parser = IEC61131Parser(CommonTokenStream(lexer))
        val ctx = parser.ilBody()
        println(ctx.toStringTree(parser))
    }

    @Test
    fun testFacade() {
        val url = LoadHelp.getResource("edu/kit/iti/formal/automation/il/p180_iec61131.il")
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
    fun testTranslate() {
        val url = LoadHelp.getResource("edu/kit/iti/formal/automation/il/p180_iec61131.il")
        Assumptions.assumeTrue(url != null)
        Files.newBufferedReader(url).use {
            val input = it.readText()
            val body = IEC61131Facade.InstructionList.parseBody(input)
            val (scope, stCode) = Il2St(body).call()
            println(IEC61131Facade.print(stCode))
        }
    }

    @Test
    fun testTranslateJmp() {
        val ilBody = parseBody(
            """LD 5
            ST A
            EQ B
            JMPC next
            LD A
            ADD B
            ST A
            next :
            ST X
            """.trimIndent(),
        )
        val (scope, stCode) = Il2St(ilBody).call()
        println(IEC61131Facade.print(stCode))
    }
}
