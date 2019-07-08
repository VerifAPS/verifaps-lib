package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import org.junit.Assert
import org.junit.Test

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

        val s = IEC61131Facade.statements(prg)
        val block = splitUpByLabel(s)
        splitGotoBlocks(block)
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

        val s = IEC61131Facade.statements(prg)
        val block = splitUpByLabel(s)
        Assert.assertEquals(4, block.blocks.size)
        Assert.assertEquals(3, block.edges.size)
        //Assert.assertEquals(s[1], block.blocks[1].statements.first())
        splitGotoBlocks(block)
        println(writeDotFile(block))
    }


    @Test
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

        val s = IEC61131Facade.statements(prg)
        val block = splitUpByLabel(s)
        Assert.assertEquals(3, block.blocks.size)
        Assert.assertEquals(2, block.edges.size)
        Assert.assertEquals(s[1], block.blocks[1].statements.first())
        splitGotoBlocks(block)
        val scope = Scope()
        scope.variables.add(VariableDeclaration("A", INT))
        scope.variables.add(VariableDeclaration("B", INT))
        scope.variables.add(VariableDeclaration("C", INT))
        scope.variables.add(VariableDeclaration("D", INT))
        scope.variables.add(VariableDeclaration("E", INT))
        fillBlocksWithMutation(block, scope)
        println(writeDotFile(block))
    }
}