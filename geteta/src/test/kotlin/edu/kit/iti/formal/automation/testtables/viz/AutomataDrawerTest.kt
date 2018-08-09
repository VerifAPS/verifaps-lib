package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.builder.AutomatonBuilderPipeline
import org.junit.Test
import org.junit.experimental.categories.Category
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */
class AutomataDrawerTest {
    @Test
    fun testSimple(): Unit {
        renderAndShow("examples/NewFile.tt.txt")
    }

    @Test
    fun testMinMax(): Unit {
        renderAndShow("examples/MinMax/MinMax.tt.txt")
    }


    private fun renderAndShow(file: String) {
        val tt = GetetaFacade.readTable(File(file))
        val pip = AutomatonBuilderPipeline(tt)
        val auto = pip.transform()
        val ad = AutomatonDrawer(File("tmp.dot"), tt, auto.automaton)
        ad.runDot = true
        ad.show = true
        ad.run()
    }
}