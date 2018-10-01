package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.viz.ODSCounterExampleWriter
import edu.kit.iti.formal.automation.testtables.viz.ODSDebugTable
import edu.kit.iti.formal.automation.testtables.viz.TableUnwinder

/**
 *
 * @author Alexander Weigl
 * @version 1 (01.10.18)
 */

object UnwindODSApp {
    @JvmStatic
    fun main(args: Array<String>) {
        UnwindODS().main(args)
    }
}

class UnwindODS : CliktCommand(
        epilog = "UnwindODS -- Tooling for Relational Test Tables.",
        name = "tt-unwind.sh") {
    val table by option("-t", "--table", help = "the xml file of the table", metavar = "FILE")
            .file()
            .required()

    val outputFile by option("-o", "--output", help = "Output ODS file")
            .file().required()

    override fun run() {
        val gtt = GetetaFacade.readTable(table)
        val unwinded = TableUnwinder(gtt, HashMap())() //use default
        val tblWriter = ODSDebugTable(gtt, unwinded)
        tblWriter.run()
        tblWriter.writer.saveAs(outputFile)
    }
}