/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.apps


import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import com.github.jferard.fastods.tool.FastOds
import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.OmegaSimplifier
import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import edu.kit.iti.formal.automation.testtables.viz.AutomatonDrawer
import edu.kit.iti.formal.automation.testtables.viz.ODSCounterExampleWriter
import edu.kit.iti.formal.smv.NuXMVOutput
import java.io.File
import java.lang.IllegalStateException

object Geteta {
    @JvmStatic
    fun main(args: Array<String>) {
        GetetaApp().main(args)
    }
}

class GetetaApp : CliktCommand(
        epilog = "Geteta -- Tooling for Generalized Test Tables.",
        name = "geteta.sh") {
    //val xmlModeOutput by option("-x", help = "enable XML mode")
    //        .flag(default = false)

    val disableSimplify by option("--no-simplify", help = "disable")
            .flag("--simplify", default = false)

    val table by option("-t", "--table", help = "the xml file of the table", metavar = "FILE")
            .file(exists = true, readable = true)
            .required()

    val outputFolder by option("-o", "--output", help = "Output directory")

    val library by option("-L", "--library", help = "library files").file().multiple()
    val program by option("-P", "--program", "-c", help = "program files").file(exists = true, readable = true).required()

    val nuxmv by option("--nuxmv", help = "Path to nuXmv binary.", envvar = "NUXMV")
            .file(exists = true)
            .required()

    val mode by option("-m", "--mode", help = "Verification Mode")
            .convert { Mode.valueOf(it) }

    val runAnalyzer by option("--row-map", help = "print out a row mapping")
            .flag("--no-row-map", default = false)

    val odsExport by option("--ods", help = "generate ods counterexample file").file()
    val odsOpen by option("--ods-open").flag()

    val drawAutomaton by option("--debug-automaton").flag(default = false)
    val showAutomaton by option("--show-automaton").flag(default = false)

    val verificationTechnique by option("-v", "--technique",
            help = "verification technique").convert { VerificationTechnique.valueOf(it) }.default(VerificationTechnique.IC3)

    override fun run() {
        Console.info("Use table file ${table.absolutePath}")
        var gtt = GetetaFacade.readTable(table.absoluteFile)

        Console.info("Apply omega simplification")

        val os = OmegaSimplifier(gtt); os.run()
        if (!os.ignored.isEmpty()) {
            gtt = os.product
            Console.warn("I ignore following rows: %s, because they are behind an \\omega duration.%n", os.ignored)
        } else Console.info("No rows unreachable!")


        //
        Console.info("Parse program ${program.absolutePath} with libraries ${library}")
        val code = IEC61131Facade.readProgramsWithLibrary(library, listOf(program))[0] ?:
                throw IllegalStateException("No program given in $program")

        if (mode != null)
            gtt.options.mode = mode!!

        Console.info("Mode is ${gtt.options.mode}")

        val modCode = SymbExFacade.evaluateProgram(code, disableSimplify)
        Console.info("Program evaluation")

        val superEnumType = GetetaFacade.createSuperEnum(listOf(code.scope))
        Console.info("Super enum built")

        val tt = GetetaFacade.constructSMV(gtt, superEnumType)
        Console.info("SMV for table constructed")

        if (drawAutomaton) {
            Console.info("Automaton drawing requested. This may took a while.")
            val ad = AutomatonDrawer(File(outputFolder, "${this.table.name}.dot"),
                    gtt, tt.automaton)
            ad.runDot = true
            ad.show = showAutomaton
            ad.run()
            if (showAutomaton)
                Console.info("Image viewer should open")
        } else {
            Console.info("For drawing the automaton use: `--draw-automaton'.")
        }

        Console.info("Constructing final SMV file.")
        val modTable = tt.tableModule
        val mainModule = GetetaFacade.glue(modTable,
                tt.ttType!!, listOf(modCode), gtt.programRuns, gtt.options)

        val modules = arrayListOf(mainModule, modTable, modCode)
        modules.addAll(tt.helperModules)

        val folder = File(this.table.parent, this.table.nameWithoutExtension).absolutePath
        Console.info("Run nuXmv: $nuxmv in $folder using ${gtt.options.verificationTechnique}")
        val b = GetetaFacade.runNuXMV(
                nuxmv.absolutePath,
                folder,
                modules,
                gtt.options.verificationTechnique)

        val status =
                when (b) {
                    NuXMVOutput.Verified -> "verified"
                    is NuXMVOutput.Error -> "error"
                    is NuXMVOutput.NotVerified -> "not-verified"
                }

        if (b is NuXMVOutput.NotVerified) {
            if (runAnalyzer) {
                val mappings = GetetaFacade.analyzeCounterExample(
                        tt.automaton, gtt, b.counterExample)
                mappings.forEachIndexed { i, m ->
                    Console.info("%3d: %s", 0, m.asRowList())
                }
                if (mappings.isEmpty()) {
                    Console.warn("no row mapping found!")
                } else if (odsExport != null) {
                    val w = ODSCounterExampleWriter(b.counterExample, gtt, mappings)
                    w.run()
                    w.writer.saveAs(odsExport)
                    FastOds.openFile(odsExport)
                } else {
                    Console.info("Use `--ods <table.ods>' to generate a counterexample tables.")
                }
            } else {
                Console.info("Use `----row-map' to print possible row mappings.")
            }
        }
        Console.info("STATUS: $status")
    }
}

