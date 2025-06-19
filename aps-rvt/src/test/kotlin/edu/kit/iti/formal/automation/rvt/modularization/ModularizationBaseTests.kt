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
package edu.kit.iti.formal.automation.rvt.modularization

import com.google.common.truth.Truth
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.st.ast.BlockStatement
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Token
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (14.07.18)
 */
class ModularizationBaseTests {
    fun testListCallSite(name: String): List<String> {
        val (pous, e) =
            IEC61131Facade.fileResolve(
                CharStreams.fromStream(
                    javaClass.getResourceAsStream(name),
                ),
            )
        val p = pous.findFirstProgram()!!
        val simplified = SymbExFacade.simplify(p)
        val cfs = ModFacade.updateBlockStatements(simplified)
        return cfs.map { it.repr() }
    }

    @Test
    fun listCallSites0() {
        val act = testListCallSite("/modularization/program.st")
        Truth.assertThat(act).containsExactly(
            "PGRM.INST_FB.0",
            "PGRM.INST_FB.1",
        )
    }

    @Test
    fun listCallSites1() {
        val act = testListCallSite("/modularization/program1.st")
        Truth.assertThat(act).containsExactly(
            "PGRM.INST_A.0",
            "PGRM.INST_B.0",
            "PGRM.TestTimer.0",
        )
    }

    @Test
    fun listCallSites2() {
        val act = testListCallSite("/modularization/program2.st")
        Truth.assertThat(act).containsExactly(
            "PGRM.INST_A.0",
            "PGRM.INST_B.0",
        )
    }

    @Test
    fun listCallSites3() {
        val act = testListCallSite("/modularization/scenario0.st")
        Truth.assertThat(act).containsExactly(
            "Main.Mag.0",
            "Main.Crane.0",
            "Main.Crane.TimeDelay_Timer.0",
        )
    }

    @Test
    fun listCallSites4() {
        val act = testListCallSite("/modularization/scenario1.st")
        Truth.assertThat(act).containsExactly(
            "Main.Mag.0",
            "Main.Crane.0",
            "Main.Crane.TimeDelay_Timer.0",
        )
    }

    @Test fun testLexer() {
        val t: Token = getFirstToken("//!region name () => ()")
        Assertions.assertEquals(IEC61131Lexer.BLOCK_START, t.type)
    }

    @Test fun testParser() {
        val p = IEC61131Facade.statements(
            """
            //!region q () => (x) 
            x := 2;
            //!end_region
            """.trimIndent(),
        )
        IEC61131Facade.print(p)
        Assertions.assertNotNull(p.first())
        Assertions.assertTrue(p.first() is BlockStatement)
    }

    private fun getFirstToken(s: String): Token {
        val lexer = IEC61131Lexer(CharStreams.fromString(s))
        return lexer.nextToken()
    }

    @Test
    fun listCallSites5() {
        val act = testListCallSite("/modularization/user_specified.st")
        Truth.assertThat(act).containsExactly(
            "main.a.0",
            "main.f.0",
        )
    }
}
