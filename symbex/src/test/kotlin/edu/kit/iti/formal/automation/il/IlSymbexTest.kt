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

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.CodeWriter
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import java.io.StringWriter

/**
 * @author Alexander Weigl
 * @version 1 (22.02.19)
 */
class IlSymbexTest {
    @Test
    fun ilSymbexFirstTest() {
        val scope = Scope.defaultScope()
        scope.variables += VariableDeclaration("A", AnyBit.BOOL)
        scope.variables += VariableDeclaration("B", AnyBit.BOOL)
        scope.variables += VariableDeclaration("X", AnyBit.BOOL)
        scope.variables += VariableDeclaration("Y", AnyBit.BOOL)

        val ilBody =
            parseBody(
                """AND (
        LD X
        OR Y
        )
        ST A
        LD TRUE
        AND( X
        OR Y
        )
        ST B
                """.trimIndent(),
            )

        val sw = StringWriter()
        ilBody.accept(IlPrinter(CodeWriter(sw)))
        println(sw)

        val symbex = IlSymbex(ilBody, 10, scope)
        val state = symbex.call()
        println(state)
        val unfolded = state.unfolded()
        val A = unfolded[SVariable("A")]
        val B = unfolded[SVariable("B")]
        Assertions.assertEquals(A, B)
    }

    @Test
    @Disabled
    fun ilSymbexJmpTest() {
        val scope = Scope.defaultScope()
        scope.variables += VariableDeclaration("A", AnyBit.BOOL)
        scope.variables += VariableDeclaration("B", AnyBit.BOOL)
        scope.variables += VariableDeclaration("X", AnyBit.BOOL)
        scope.variables += VariableDeclaration("Y", AnyBit.BOOL)

        val ilBody =
            parseBody(
                """LD 5
            ST A
            EQ B
            JMPC next
            LD A
            ADD B
            ST A
            next:
            ST X
                """.trimIndent(),
            )

        val sw = StringWriter()
        ilBody.accept(IlPrinter(CodeWriter(sw)))
        println(sw)

        val symbex = IlSymbex(ilBody, 10, scope)
        val state = symbex.call()
        println(state)
        val A = state["A"]
        val B = state["B"]
        Assertions.assertEquals(A, B)
    }

    private fun parseBody(s: String) = IEC61131Facade.InstructionList.parseBody(s)
}