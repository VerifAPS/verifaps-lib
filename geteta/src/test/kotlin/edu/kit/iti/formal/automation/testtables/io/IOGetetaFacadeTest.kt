package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.TableTester
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (06.07.18)
 */
class IOGetetaFacadeTest : TableTester() {
    @Test
    fun testGrammar() {
        val resourceAsStream = javaClass.getResourceAsStream("/dsl/detwait3.tt.txt")
        Assumptions.assumeTrue(resourceAsStream != null)
        val gtt = GetetaFacade.parseTableDSL(CharStreams.fromStream(resourceAsStream))
        println(gtt)
    }
}