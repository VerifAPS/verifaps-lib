package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.convert
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.monitor.MonitorGenerationST

/**
 *
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */
object Monitor {
    @JvmStatic
    fun main(args: Array<String>) = MonitorApp().main(args)
}

enum class CodeOutput {
    STRCUTURED_TEXT, ESTEREL, CPP
}

class MonitorApp : CliktCommand(name = "ttmonitor",
        help = "Construction of monitors from test tables for Runtime Verification") {
    val table by option("--table,-t", help = "table file", metavar = "FILE")
            .file(exists = true, readable = true).required()

    val format by option("--format", "-f", help = "code format, possible values: " +
            CodeOutput.values().joinToString(",") { it.name })
            .convert { CodeOutput.valueOf(it) }.default(CodeOutput.STRCUTURED_TEXT)

    override fun run() {
        val gtt = GetetaFacade.readTable(table)
        gtt.ensureProgramRuns()
        gtt.generateSmvExpression()
        val automaton = GetetaFacade.constructTable(gtt).automaton

        val output =
                when (format) {
                    CodeOutput.STRCUTURED_TEXT ->
                        MonitorGenerationST.generate(gtt, automaton)
                    CodeOutput.ESTEREL -> TODO()
                    CodeOutput.CPP -> TODO()
                }
        println(output)
    }
}