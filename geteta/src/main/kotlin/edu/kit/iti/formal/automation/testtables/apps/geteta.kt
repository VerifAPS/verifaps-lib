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

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.MultiModelGluer
import edu.kit.iti.formal.automation.testtables.builder.SMVConstructionModel
import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import edu.kit.iti.formal.automation.testtables.viz.AutomatonDrawer
import edu.kit.iti.formal.automation.testtables.viz.CounterExamplePrinterWithProgram
import edu.kit.iti.formal.automation.testtables.viz.ODSCounterExampleWriter
import edu.kit.iti.formal.smv.NuXMVOutput
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.findProgram
import edu.kit.iti.formal.util.info
import edu.kit.iti.formal.util.warn
import java.io.File
import kotlin.system.exitProcess

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
            .multiple(required = true)

    val outputFolder by option("-o", "--output", help = "Output directory")

    val library by option("-L", "--library", help = "library files").file().multiple()
    val program by option("-P", "--program", "-c", help = "program files").file(exists = true, readable = true).required()

    val nuxmv by option("--nuxmv",
            help = "Path to nuXmv binary. You can also set the environment variable \$NUXMV",
            envvar = "NUXMV")
            .default("nuXmv")

    val mode by option("-m", "--mode", help = "Verification Mode")
            .convert { Mode.valueOf(it) }

    val runAnalyzer by option("--row-map", help = "print out a row mapping")
            .flag("--no-row-map", default = false)

    val odsExport by option("--ods", help = "generate ods counterexample file").file()
    val odsOpen by option("--ods-open").flag()

    val cexPrinter by option("--cexout", help = "prints an analysation of the counter example and the program")
            .flag()

    val drawAutomaton by option("--debug-automaton").flag(default = false)
    val showAutomaton by option("--show-automaton").flag(default = false)

    val verificationTechnique by option("-v", "--technique",
            help = "verification technique").convert { VerificationTechnique.valueOf(it) }
            .default(VerificationTechnique.IC3)

    override fun run() {
        val gtts = table.flatMap {
            info("Use table file ${it.absolutePath}")
            GetetaFacade.readTables(it)
        }.map {
            it.ensureProgramRuns()
            it.generateSmvExpression()
            it.simplify()
        }

        //
        info("Parse program ${program.absolutePath} with libraries ${library}")
        val code = IEC61131Facade.readProgramsWLP(library, listOf(program)).first()
                ?: throw IllegalStateException("No program given in $program")

        // override mode
        if (mode != null)
            gtts.forEach { it.options.mode = mode!! }

        gtts.forEach {
            info("Mode is ${it.options.mode} for table ${it.name}")
        }

        val (lineMap, modCode) = SymbExFacade.evaluateProgramWithLineMap(code, disableSimplify)
        info("Program evaluation")

        val superEnumType = GetetaFacade.createSuperEnum(listOf(code.scope))
        info("Super enum built")

        val tt = gtts.map { gtt -> GetetaFacade.constructSMV(gtt, superEnumType) }
        info("SMV for table constructed")

        if (drawAutomaton) {
            info("Automaton drawing requested. This may took a while.")
            gtts.zip(tt).forEach { (gtt, tt) ->
                val ad = AutomatonDrawer(File(outputFolder, "${gtt.name}.dot"),
                        gtt, tt.automaton)
                ad.runDot = true
                ad.show = showAutomaton
                ad.run()
                if (showAutomaton)
                    info("Image viewer should open now")
            }
        } else {
            info("For drawing the automaton use: `--draw-automaton'.")
        }

        info("Constructing final SMV file.")
        val modTable = tt.map { it.tableModule }
        val mainModule = MultiModelGluer().apply {
            val pn = gtts.first().programRuns.first() // only one run in geteta
            addProgramRun(pn, modCode)
            tt.forEach {
                addTable("_" + it.testTable.name, it.ttType!!)
            }
        }
        val modules = arrayListOf(mainModule.product, modCode)
        modules.addAll(modTable)
        tt.forEach { modules.addAll(it.helperModules) }

        val folder = File(this.table.first().parent,
                this.table.first().nameWithoutExtension).absolutePath
        val verificationTechnique = gtts.first().options.verificationTechnique
        info("Run nuXmv: $nuxmv in $folder using ${verificationTechnique}")
        val nuxmv = findProgram(nuxmv)
        if (nuxmv == null) {
            error("Could not find ${this.nuxmv}.")
            exitProcess(1)
            return
        }
        val b = GetetaFacade.runNuXMV(
                nuxmv.absolutePath,
                folder,
                modules,
                verificationTechnique)

        val status =
                when (b) {
                    NuXMVOutput.Verified -> "verified"
                    is NuXMVOutput.Error -> "error"
                    is NuXMVOutput.Cex -> "not-verified"
                }

        val errorLevel =
                when (b) {
                    is NuXMVOutput.Error -> 1
                    else -> 0
                }

        if (b is NuXMVOutput.Cex) {
            if (cexPrinter) useCounterExamplePrinter(outputFolder, b, tt, lineMap, code)
            else info("Use `--cexout' to print a cex analysation.")
            if (runAnalyzer) runCexAnalysation(b, tt)
            else info("Use `--row-map' to print possible row mappings.")
        }
        info("STATUS: $status")
        exitProcess(errorLevel)
    }

    private fun runCexAnalysation(result: NuXMVOutput.Cex, tt: List<SMVConstructionModel>) {
        val mappings = tt.map {
            GetetaFacade.analyzeCounterExample(
                    it.automaton, it.testTable, result.counterExample)
        }

        mappings.forEach { mapping ->
            info("MAPPING: ==========")
            mapping.forEachIndexed { i, m ->
                info("{}: {}", i, m.asRowList())
            }
            info("/End of MAPPING")
        }

        when {
            mappings.isEmpty() -> warn("no row mapping found!")
            odsExport == null -> info("Use `--ods <table.ods>' to generate a counterexample tables.")
            odsExport != null -> {
                val w = ODSCounterExampleWriter(result.counterExample)
                tt.zip(mappings).forEach { (t, m) ->
                    w.addTestTable(t, m)
                }
                w.run()
                w.writer.saveAs(odsExport)
                FastOds.openFile(odsExport)
            }
        }
    }
}

fun useCounterExamplePrinter(
        outputFolder: String?, result: NuXMVOutput.Cex, tt: List<SMVConstructionModel>,
        lineMap: LineMap, program: PouExecutable) {
    for (model in tt) {
        val file = File(outputFolder, "cex_${model.testTable.name}.txt")
        file.bufferedWriter().use {
            val stream = CodeWriter(it)
            val cep = CounterExamplePrinterWithProgram(
                    automaton = model.automaton,
                    testTable = model.testTable,
                    cex = result.counterExample,
                    lineMap = lineMap,
                    program = program,
                    stream = stream)
            cep.getAll()
        }
    }
}

