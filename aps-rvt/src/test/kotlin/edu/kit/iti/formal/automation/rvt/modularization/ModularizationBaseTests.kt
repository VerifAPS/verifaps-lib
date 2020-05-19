package edu.kit.iti.formal.automation.rvt.modularization

import com.google.common.truth.Truth
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.st.ast.BlockStatement
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
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
                IEC61131Facade.fileResolve(CharStreams.fromStream(
                        javaClass.getResourceAsStream(name)))
        val p = pous.findFirstProgram()!!
        val simplified = SymbExFacade.simplify(p)
        val cfs = ModFacade.updateBlockStatements(simplified)
        return cfs.map { it.repr() }
    }

    @Test
    fun listCallSites0() {
        val act = testListCallSite("/modularization/program.st")
        Truth.assertThat(act).containsExactly(
                "PGRM.INST_FB.0", "PGRM.INST_FB.1")
    }

    @Test
    fun listCallSites1() {
        val act = testListCallSite("/modularization/program1.st")
        Truth.assertThat(act).containsExactly(
                "PGRM.INST_A.0",
                "PGRM.INST_B.0",
                "PGRM.TestTimer.0")
    }

    @Test
    fun listCallSites2() {
        val act = testListCallSite("/modularization/program2.st")
        Truth.assertThat(act).containsExactly(
                "PGRM.INST_A.0",
                "PGRM.INST_B.0")
    }

    @Test
    fun listCallSites3() {
        val act = testListCallSite("/modularization/scenario0.st")
        Truth.assertThat(act).containsExactly(
                "Main.Mag.0", "Main.Crane.0", "Main.Crane.TimeDelay_Timer.0")
    }

    @Test
    fun listCallSites4() {
        val act = testListCallSite("/modularization/scenario1.st")
        Truth.assertThat(act).containsExactly(
                "Main.Mag.0", "Main.Crane.0", "Main.Crane.TimeDelay_Timer.0")
    }

    @Test fun testLexer() {
        val t : Token = getFirstToken("//!region name () => ()");
        Assertions.assertEquals(IEC61131Lexer.BLOCK_START, t.type)
    }

    @Test fun testParser() {
        val p = IEC61131Facade.statements("""
            //!region q () => (x) 
            x := 2;
            //!end_region
        """.trimIndent())
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
                "main.a.0", "main.f.0")
    }
}