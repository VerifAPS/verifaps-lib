package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.util.info

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/21/20)
 */
object Synth {
    @JvmStatic
    fun main(args: Array<String>) {
        SynthApp().main(args)
    }
}

class SynthApp : CliktCommand(
        epilog = "ttsynth -- Program Coverage with Test Tables.",
        name = "ttsynth") {

    val table by argument(name = "tables", help = "the xml file of the table")
            .file(exists = true, readable = true)

    val outputFolder by option("-o", "--output", help = "Output directory")

    private fun readTable() = table.let {
        info("Use table file ${it.absolutePath}")
        GetetaFacade.readTables(it)
    }.map {
        it.ensureProgramRuns()
        it.generateSmvExpression()
        it.simplify()
    }

    override fun run() {
        val gtts = readTable()
        val automata = GetetaFacade.constructTable(gtts.first())

    }
}












