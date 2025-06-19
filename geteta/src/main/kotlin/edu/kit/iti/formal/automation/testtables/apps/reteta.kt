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
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import edu.kit.iti.formal.automation.*
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.automation.st0.TransformationState
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.MultiModelGluer
import edu.kit.iti.formal.automation.testtables.algorithms.OmegaSimplifier
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.chapterMarksForProgramRuns
import edu.kit.iti.formal.automation.testtables.rtt.RTTCodeAugmentation
import edu.kit.iti.formal.automation.testtables.viz.AutomatonDrawer
import edu.kit.iti.formal.automation.testtables.viz.CounterExampleTablePrinter
import edu.kit.iti.formal.smv.NuXMVOutput
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.fail
import edu.kit.iti.formal.util.info
import edu.kit.iti.formal.util.warn
import java.io.File
import java.util.*
import kotlin.system.exitProcess

object RetetaApp {
    @JvmStatic
    fun main(args: Array<String>) {
        try {
            Reteta().main(args)
        } catch (e: Throwable) {
            e.printStackTrace()
            exitProcess(-1)
        }
    }
}

class Reteta : CliktCommand(name = "reteta") {
    override fun helpEpilog(context: Context) = "Reteta -- Tooling for Relational Test Tables."

    val common by CommonArguments()
    val tableOptions by TableArguments()
    val programOptions by ProgramOptions()
    val outputFolder by outputFolder()
    val nuxmv by nuxmv()
    val dryRun by dryRun()
    val automatonOptions by AutomataOptions()

    val printAugmentedPrograms by option(help = "prints the augmented programs into files: <name>.st").flag()

    override fun run() {
        common.enableVerbosity()

        if (tableOptions.table.isEmpty() || programOptions.program.isEmpty()) {
            fail("No code or table file given.")
        }

        // read program
        val programs = readPrograms()
        val superEnumType = GetetaFacade.createSuperEnum(programs.map { it.scope })

        // read table
        val gtts = tableOptions.table.flatMap { GetetaFacade.readTables(it) }.map {
            it.simplify()
        }

        gtts.forEach { table ->
            val chapterMarks = table.chapterMarksForProgramRuns
            val augmentedPrograms: List<SMVModule> = programs.mapIndexed { idx, exec ->
                val rttPipeline = RTTCodeAugmentation(false, chapterMarks[idx]!!)
                val s = rttPipeline.transform(TransformationState(exec))
                val p = ProgramDeclaration(exec.name, s.scope, s.stBody)

                if (printAugmentedPrograms) {
                    File(outputFolder).mkdirs()
                    val out = File(outputFolder, "${exec.name}_$idx.st")
                    out.bufferedWriter().use {
                        IEC61131Facade.printTo(it, p)
                    }
                    info("Write augmented program into $out.")
                }

                SymbExFacade.evaluateProgram(p, true).also {
                    it.name = "${it.name}_$idx" // rename module, otherwise clash on self-compositions
                }
            }

            if (!table.options.relational) {
                throw IllegalStateException()
            }

            val tt = GetetaFacade.constructSMV(table, superEnumType)

            if (automatonOptions.drawAutomaton) {
                info("Automaton drawing requested. This may took a while.")
                val ad = AutomatonDrawer(
                    File(outputFolder, "${table.name}.dot"),
                    listOf(table.region),
                    tt.automaton,
                )
                ad.runDot = true
                ad.show = automatonOptions.showAutomaton
                ad.run()
                if (automatonOptions.showAutomaton) {
                }
                info("Image viewer should open now")
            } else {
                info("For drawing the automaton use: `--draw-automaton'.")
            }

            val out = GetetaFacade.print(table)
            File(outputFolder, "table.gtt").bufferedWriter().use { it.write(out) }

            val modTable = tt.tableModule
            val mainModule = MultiModelGluer().apply {
                table.programRuns.zip(augmentedPrograms).forEach { (n, p) ->
                    addProgramRun(n, p)
                }
                addTable("_${table.name}", tt.ttType!!)
            }

            val modules = LinkedList<SMVModule>()
            modules.add(mainModule.product)
            modules.add(modTable)
            modules.addAll(augmentedPrograms)
            modules.addAll(tt.helperModules)
            val pNuxmv = GetetaFacade.createNuXMVProcess(
                outputFolder,
                modules,
                nuxmv ?: "nuxmv",
                table.options.verificationTechnique,
            )
            if (dryRun) {
                val b = pNuxmv.call()
                when (b) {
                    NuXMVOutput.Verified -> {
                        info("Verified!")
                    }

                    is NuXMVOutput.Cex -> {
                        info("Not verified. Counter example available.")
                        File(outputFolder, "counterexample.txt").bufferedWriter().use {
                            CounterExampleTablePrinter(tt.automaton, table, b.counterExample, CodeWriter(it)).print()
                        }
                        /*else info("Use `--cexout' to print a cex analysation.")
                            if (runAnalyzer) runCexAnalysation(b, tt)
                            else info("Use `--row-map' to print possible row mappings.")
                         */
                        exitProcess(67)
                    }

                    is NuXMVOutput.Error -> {
                        for (e in b.errors) {
                            error(e)
                        }
                        exitProcess(1)
                    }
                }
            } else {
                info("Model checker skipped due to `--dont-model-check` flag.")
            }
        }
    }

    fun readPrograms(): List<PouExecutable> {
        info("Provided library code: ${programOptions.library}")
        info("Reading programs (in order): ${programOptions.program}")
        val programs = IEC61131Facade.readProgramsWLPN(programOptions.library, programOptions.program)
        val nullIndex = programs.indexOf(null)
        if (nullIndex >= 0) {
            fail("Could not find an executable pou in '${programOptions.program[nullIndex]}'.")
        } else {
            return programs.filterNotNull().toMutableList()
        }
    }
}

internal fun GeneralizedTestTable.simplify(): GeneralizedTestTable {
    info("Apply omega simplification")
    val os = OmegaSimplifier(this)
    os.run()
    if (!os.ignored.isEmpty()) {
        warn("I ignore following rows: %s, because they are behind an \\omega duration.%n", os.ignored)
        return os.product
    }
    info("No rows unreachable!")
    return this
}