package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.convert
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.ConstraintVariable
import edu.kit.iti.formal.automation.testtables.monitor.CMonitorGenerator
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
    STRCUTURED_TEXT, ESTEREL, CPP,C
}

class MonitorApp : CliktCommand(name = "ttmonitor",
        help = "Construction of monitors from test tables for Runtime Verification") {
    val table by option("--table","-t", help = "table file", metavar = "FILE")
            .file(exists = true, readable = true).required()

    val format by option("--format", "-f", help = "code format, possible values: " +
            CodeOutput.values().joinToString(",") { it.name })
            .convert { CodeOutput.valueOf(it.toUpperCase()) }.default(CodeOutput.STRCUTURED_TEXT)

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
                    CodeOutput.C -> CMonitorGenerator.generate(gtt,automaton)
                    CodeOutput.CPP -> TODO()
                }
        println(output)
    }
}


fun bindsConstraintVariable(ctx: TestTableLanguageParser.CellContext?, fvar: ConstraintVariable): Boolean {
    return ctx?.chunk()?.filter { chunk ->
        val variable = chunk.variable()
        val ss = chunk.singlesided()
        if (ss != null) {
            val e = ss.expr() as? TestTableLanguageParser.VariableContext
            if (e == null || ss.relational_operator().text == "=") false
            else e.IDENTIFIER().equals(fvar.name)
        } else if (variable != null) {
            variable.IDENTIFIER().text == fvar.name
        } else
            false
    }?.isNotEmpty() ?: false
}