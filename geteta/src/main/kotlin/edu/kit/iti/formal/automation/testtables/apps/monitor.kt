/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.groups.provideDelegate
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.ConstraintVariable
import edu.kit.iti.formal.automation.testtables.monitor.*
import edu.kit.iti.formal.util.info
import java.io.File
import java.util.*

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
    /*STRCUTURED_TEXT, ESTEREL, */
    CPP, // , C
}

class MonitorApp : CliktCommand(name = "ttmonitor") {
    override fun help(context: Context) = "Construction of monitors from test tables for Runtime Verification"

    val tableOptions by TableArguments()

    val output by option("--output", "-o", help = "destination of the output file")
        .file()
        .default(File("output.cpp"))

    val writeHeader by option("--write-header", help = "Write the 'monitor.h' header file.")
        .flag("--dont-write-header", default = false)

    val format by option(
        "--format",
        "-f",
        help = "code format, possible values: " +
            CodeOutput.entries.joinToString(",") { it.name },
    )
        .convert { CodeOutput.valueOf(it.uppercase(Locale.getDefault())) }
        .default(CodeOutput.CPP)

    val disableCombinedMonitor by option(
        "--disable-combined",
        help = "Generate a combined monitored or single monitors of given tables",
    ).flag("--combined")

    val includes by option("-I", help = "give header files to be included").multiple()

    override fun run() {
        info("Files: ${tableOptions.table}")
        info("Filter: ${tableOptions.tableWhitelist}")

        if (writeHeader && format == CodeOutput.CPP) {
            output.absoluteFile.parentFile.mkdirs()
            for ((a, b) in CPP_RESOURCES) {
                info("Write resource file $a.")
                File(output.absoluteFile.parentFile, a).bufferedWriter().use { it.write(b) }
            }
        }

        val gtts = tableOptions.readTables()
        info("Tables: ${gtts.joinToString { it.name }}")

        val pairs = gtts.map { it to GetetaFacade.constructTable(it).automaton }

        val options = MonitorGenerationOptions(includes = includes)

        val output =
            if (gtts.size == 1 || disableCombinedMonitor) {
                val monitor = Monitor()
                for ((gtt, automaton) in pairs) {
                    val m = when (format) {
                        // CodeOutput.STRCUTURED_TEXT -> MonitorGenerationST.generate(gtt, automaton)
                        // CodeOutput.ESTEREL -> TODO()
                        // CodeOutput.C -> CMonitorGenerator.generate(gtt, automaton)
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
                    // else -> TODO()
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

fun bindsConstraintVariable(ctx: TestTableLanguageParser.CellContext?, fvar: ConstraintVariable): Boolean =
    ctx?.chunk()?.filter { chunk ->
        val ss = chunk.getChild(0)
        when (ss) {
            is TestTableLanguageParser.SinglesidedContext -> {
                val expr = ss.expr()
                val e = expr as? TestTableLanguageParser.BvariableContext
                val v = e?.variable()?.IDENTIFIER()
                if (v == null || ss.relational_operator().text == "=") {
                    false
                } else {
                    v.equals(fvar.name)
                }
            }
            is TestTableLanguageParser.CvariableContext -> {
                ss.variable().IDENTIFIER().text == fvar.name
            }
            else -> false
        }
    }?.isNotEmpty() ?: false