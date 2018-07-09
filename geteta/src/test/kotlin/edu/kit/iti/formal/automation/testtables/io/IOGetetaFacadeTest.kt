package edu.kit.iti.formal.automation.testtables.io

import org.antlr.v4.runtime.CharStreams
import org.junit.Assume
import org.junit.Test

/**
 * @author Alexander Weigl
 * @version 1 (06.07.18)
 */
class IOGetetaFacadeTest {
    @Test
    fun testGrammar() {
        val resourceAsStream = javaClass.getResourceAsStream("/dsl/detwait3.tt.txt")
        Assume.assumeNotNull(resourceAsStream)
        val gtt = IOFacade.parseTable(CharStreams.fromStream(
                resourceAsStream))
        println(gtt)
    }
}