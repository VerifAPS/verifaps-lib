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

        val ilBody = parseBody("""AND (
        LD X
        OR Y
        )
        ST A
        LD TRUE
        AND( X
        OR Y
        )
        ST B
        """.trimIndent())

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

        val ilBody = parseBody("""LD 5
            ST A
            EQ B
            JMPC next
            LD A
            ADD B
            ST A
            next:
            ST X
        """.trimIndent())

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