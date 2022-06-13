package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.builder.AutomatonBuilderPipeline
import org.junit.jupiter.api.Test
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */
class AutomataDrawerTest {
    @Test
    fun testSimple() =
            renderAndShow("examples/NewFile.gtt")

    @Test
    fun testMinMax() = renderAndShow("examples/MinMax/MinMax.tt.txt")


    private fun renderAndShow(file: String) {
        val tt = GetetaFacade.readTables(File(file)).first()
        val pip = AutomatonBuilderPipeline(tt)
        val auto = pip.transform()
        val ad = AutomatonDrawer(File("tmp.dot"), listOf(tt.region), auto.automaton)
        ad.runDot = true
        ad.show = true
        ad.run()
    }
}