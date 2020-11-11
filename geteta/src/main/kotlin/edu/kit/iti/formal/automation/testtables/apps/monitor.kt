package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.ConstraintVariable
import edu.kit.iti.formal.automation.testtables.monitor.*
import edu.kit.iti.formal.automation.testtables.monitor.Monitor
import edu.kit.iti.formal.util.info
import java.io.File

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
    STRCUTURED_TEXT, ESTEREL, CPP, C
}

class MonitorApp : CliktCommand(name = "ttmonitor",
        help = "Construction of monitors from test tables for Runtime Verification") {
    val table by argument(help = "table file", name = "FILE")
            .file(exists = true, readable = true)
            .multiple(required = true)

    val output by option("--output", "-o", help = "destination to write output files")
            .file()
            .default(File("output.cpp"))

    val filter by option("--monitor", "-m", help = "manually select the gtts").multiple()

    val writeHeader by option("--write-header", help = "Write the 'monitor.h' header file.")
            .flag("--dont-write-header", default = false)

    val format by option("--format", "-f", help = "code format, possible values: " +
            CodeOutput.values().joinToString(",") { it.name })
            .convert { CodeOutput.valueOf(it.toUpperCase()) }
            .default(CodeOutput.CPP)

    val disableCombinedMonitor by option("--disable-combined").flag("--combined")

    val includes by option("-I").multiple()

    override fun run() {
        info("Files: $table")
        info("Filter: $filter")

        if (writeHeader && format == CodeOutput.CPP) {
            output.absoluteFile.parentFile.mkdirs()
            for ((a, b) in CPP_RESOURCES) {
                info("Write resource file $a.")
                File(output.absoluteFile.parentFile, a).bufferedWriter().use { it.write(b) }
            }
        }

        val gtts = table.flatMap { GetetaFacade.readTables(it) }.map {
            it.ensureProgramRuns()
            it.generateSmvExpression()
            it
        }.filter { filter.isEmpty() || it.name in filter }
        info("Tables: ${gtts.joinToString { it.name }}")


        val pairs = gtts.map { it to GetetaFacade.constructTable(it).automaton }

        val options = MonitorGenerationOptions(includes = includes)

        val output =
                if (gtts.size == 1 || disableCombinedMonitor) {
                    val monitor = Monitor()
                    for ((gtt, automaton) in pairs) {
                        val m = when (format) {
                            CodeOutput.STRCUTURED_TEXT -> MonitorGenerationST.generate(gtt, automaton)
                            CodeOutput.ESTEREL -> TODO()
                            CodeOutput.C -> CMonitorGenerator.generate(gtt, automaton)
                            CodeOutput.CPP -> CppMonitorGenerator.generate(gtt, automaton, options)
                        }
                        monitor.preamble = m.preamble
                        monitor.types += m.types
                        monitor.body += m.body
                        monitor.postamble = m.postamble
                    }
                    monitor
                } else {
                    when (format) {
                        CodeOutput.CPP -> CppCombinedMonitorGeneration.generate("mcombined", pairs)
                        else -> TODO()
                    }
                }
        this.output.bufferedWriter().use {
            it.write(output.preamble)
            it.write(output.types)
            it.write(output.body)
            it.write(output.postamble)
        }
    }
}


fun bindsConstraintVariable(ctx: TestTableLanguageParser.CellContext?, fvar: ConstraintVariable): Boolean {
    return ctx?.chunk()?.filter { chunk ->
        val ss = chunk.getChild(0)
        when (ss) {
            is TestTableLanguageParser.SinglesidedContext -> {
                val e = ss.expr() as? TestTableLanguageParser.VariableContext
                if (e == null || ss.relational_operator().text == "=") false
                else e.IDENTIFIER().equals(fvar.name)
            }
            is TestTableLanguageParser.CvariableContext -> {
                ss.variable().IDENTIFIER().text == fvar.name
            }
            else -> false
        }
    }?.isNotEmpty() ?: false
}