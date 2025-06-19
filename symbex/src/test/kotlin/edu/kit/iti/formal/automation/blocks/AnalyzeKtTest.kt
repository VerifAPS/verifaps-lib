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
package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.IEC61131Facade.expr
import edu.kit.iti.formal.automation.IEC61131Facade.statements
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test

internal class AnalyzeKtTest {
    @Test
    fun emptyProgram() {
        val block = splitUpByLabel(StatementList())
        println(writeDotFile(block))
    }

    @Test
    fun smallestJumpProgram() {
        val prg = """
             JMP A;
             A: a:=1;
        """.trimIndent()

        val s = statements(prg)
        val block = splitUpByLabel(s)
        splitGotoBlocks(block)
        println(writeDotFile(block))
    }

    @Test
    fun smallestLoopWithJumpProgram() {
        val prg = """
             A: 
                a:=1;
             B:
              JMP A;
        """.trimIndent()

        val s = statements(prg)
        val block = splitUpByLabel(s)
        splitGotoBlocks(block)
        block.unrollLoop(block.blocks.subList(1, 3).toMutableList(), 1)
        println(writeDotFile(block))
    }

    @Test
    fun selfLoopWithJumpProgram() {
        val prg = """
             A: 
              a:=1;
              JMP A;
        """.trimIndent()

        val s = statements(prg)
        val block = splitUpByLabel(s)
        splitGotoBlocks(block)
        println(writeDotFile(block))
        block.unrollLoops()
        println(writeDotFile(block))
    }

    @Test
    fun ifProgram() {
        val prg = """
            IF abc THEN
                JMP A;
             ELSEIF q=2 THEN
                JMP B;
             END_IF

             A: a:=1;
             B: b:=1;
        """.trimIndent()

        val s = statements(prg)
        val block = splitUpByLabel(s)
        Assertions.assertEquals(4, block.blocks.size)
        Assertions.assertEquals(3, block.edges.size)
        // Assert.assertEquals(s[1], block.blocks[1].statements.first())
        splitGotoBlocks(block)
        println(writeDotFile(block))
    }

    @Test @Disabled
    fun ifGotoProgram() {
        val prg = """
            LBL:
            IF A=B THEN
                A:=1;
                B:=2;
                C:=3;
                IF a=1 THEN
                    JMP LBL;
                ELSE
                    B:=4;
                END_IF
                D:=5;
             ELSEIF E=B THEN
                E:=3;
             END_IF
        """.trimIndent()

        val s = statements(prg)
        val block = splitUpByLabel(s)
        Assertions.assertEquals(3, block.blocks.size)
        Assertions.assertEquals(2, block.edges.size)
        Assertions.assertEquals(s[1], block.blocks[1].statements.first())
        splitGotoBlocks(block)
        val scope = Scope()
        scope.variables.add(VariableDeclaration("A", INT))
        scope.variables.add(VariableDeclaration("B", INT))
        scope.variables.add(VariableDeclaration("C", INT))
        scope.variables.add(VariableDeclaration("D", INT))
        scope.variables.add(VariableDeclaration("E", INT))
        block.ssa()
        println(writeDotFile(block))
    }

    @Test @Disabled
    fun testSSA() {
        val bp = BlockProgram()
        val b1 = Block("b1", statements = statements("c:= (a=1); e := 7+e;"))
        val b2 = Block("b2", expr("c"), statements("b := e/6;"))
        val b3 = Block("b3", expr("NOT c"), statements("a:=1; b := e+2;"))
        val b4 = Block("b4", expr("TRUE"), statements("a:=5+a; b := 3+a+b;"))

        bp.blocks.add(b1)
        bp.blocks.add(b2)
        bp.blocks.add(b3)
        bp.blocks.add(b4)
        bp.edges += b1 to b2
        bp.edges += b1 to b3
        bp.edges += b2 to b4
        bp.edges += b3 to b4

        bp.scope.variables.add(VariableDeclaration("a", INT))
        bp.scope.variables.add(VariableDeclaration("b", INT))
        bp.scope.variables.add(VariableDeclaration("c", INT))
        bp.scope.variables.add(VariableDeclaration("d", INT))
        bp.scope.variables.add(VariableDeclaration("e", INT))
        println(writeDotFile(bp))
        bp.ssa()
        println(writeDotFile(bp))

        val actual = StringBuilder()
        bp.endBlock.ssaMutation.forEach { t, u ->
            actual.append("${t.name} ==> ${u.repr()}\n\n")
        }

        val expected = """__ERROR__ ==> __ERROR__
            
a ==> 0sd16_5 + (case 
a = 0sd16_1 : a; !(a = 0sd16_1) : 0sd16_1; 
esac)

b ==> 0sd16_3 + 0sd16_5 + (case 
a = 0sd16_1 : a; !(a = 0sd16_1) : 0sd16_1; 
esac) + (case 
a = 0sd16_1 : (0sd16_7 + e) / 0sd16_6; !(a = 0sd16_1) : 0sd16_7 + e + 0sd16_2; 
esac)

c ==> a = 0sd16_1

d ==> d

e ==> 0sd16_7 + e
        """.trimIndent()
        Assertions.assertEquals(expected.trim(), actual.trim())
    }
}
