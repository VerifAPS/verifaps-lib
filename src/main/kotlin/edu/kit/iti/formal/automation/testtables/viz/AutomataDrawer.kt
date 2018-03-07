package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.testtables.model.Automata
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
class AutomataDrawer(val outputFile: File, val automata: Automata) : Runnable {
    val runDot: Boolean = false
    val show: Boolean = false
    val style: Map<String, String> = HashMap()

    override fun run() {
        createDot()
        if (runDot) {
            doDot()
            if (show) doShow()
        }

    }

    private fun createDot() {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    private fun doShow() {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    private fun doDot() {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}