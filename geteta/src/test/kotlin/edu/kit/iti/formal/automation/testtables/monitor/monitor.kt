package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.07.19)
 */
class MonitorTests {
    @Test
    fun testSimple() {
        val file = File("examples/constantprogram/constantprogram.gtt")
        Assumptions.assumeTrue(file.exists())
        val gtt = GetetaFacade.parseTableDSL(file)
        gtt.programRuns += ""
        gtt.generateSmvExpression()
        val automaton = GetetaFacade.constructTable(gtt).automaton
        val mon = CppMonitorGenerator.generate(gtt, automaton)
        println(mon)
    }
}