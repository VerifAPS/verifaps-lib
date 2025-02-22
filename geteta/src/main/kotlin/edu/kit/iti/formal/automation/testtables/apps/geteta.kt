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
import com.github.ajalt.clikt.core.Context
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.groups.provideDelegate
import com.github.ajalt.clikt.parameters.options.convert
import com.github.ajalt.clikt.parameters.options.option
import com.github.jferard.fastods.tool.FastOds
import edu.kit.iti.formal.automation.*
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.HccPrinter
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st0.trans.SCOPE_SEPARATOR
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.MultiModelGluer
import edu.kit.iti.formal.automation.testtables.builder.*
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import edu.kit.iti.formal.automation.testtables.viz.*
import edu.kit.iti.formal.smv.NuXMVOutput
import edu.kit.iti.formal.util.*
import java.io.File
import kotlin.system.exitProcess

object Geteta {
    @JvmStatic
    fun main(args: Array<String>) {
        GetetaApp().main(args)
    }
}

class GetetaApp : CliktCommand(name = "geteta") {
    override fun helpEpilog(context: Context) = "Geteta -- Tooling for Generalized Test Tables."

    val programOptions by ProgramOptions()
    val tableOptions by TableArguments()
    val outputFolder by outputFolder()
    val dryRun by dryRun()
    val nuxmv by nuxmv()

    val cexAnalysation by CexAnalysationArguments()

    val automataOptions by AutomataOptions()

    val mode by option("-m", "--mode", help = "verification mode")
        .convert { Mode.valueOf(it) }

    override fun run() {
        val gtts = tableOptions.readTables()

        //
        info("Parse program ${programOptions.program.first()} with libraries ${programOptions.library}")
        val code = programOptions.readProgram()

        // override mode
        mode?.let { m ->
            gtts.forEach { it.options.mode = m }
        }

        gtts.forEach {
            info("Mode is ${it.options.mode} for table ${it.name}")
        }

        val (lineMap, modCode) = SymbExFacade.evaluateProgramWithLineMap(
            code,
            programOptions.disableSimplify
        )
        info("Program evaluation")

        val superEnumType = GetetaFacade.createSuperEnum(listOf(code.scope))
        info("Super enum built")

        val tt = gtts.map { gtt -> GetetaFacade.constructSMV(gtt, superEnumType) }
        info("SMV for table constructed")

        if (automataOptions.drawAutomaton) {
            info("Automaton drawing requested. This may took a while.")
            gtts.zip(tt).forEach { (gtt, tt) ->
                drawAutomaton(gtt, tt)
            }
        } else {
            info("For drawing the automaton use: `--draw-automaton'.")
        }

        val modules =
            if (tableOptions.enableMesh) {
                warn("mesh gtt support is experimental and not well-tested or completely implemented!!!")
                warn("YOU HAVE BEEN WARNED.")
                val tableJoiner = GetetaFacade.meshTables(tt)
                val dummyGtt = GetetaFacade.createMeshedDummy(gtts)
                val smv = GetetaFacade.constructSMV(
                    AutomataTransformerState(dummyGtt, tableJoiner), superEnumType
                )

                if (automataOptions.drawAutomaton) {
                    info("Automaton drawing requested. Drawing the meshed automaton.")
                    drawAutomaton(tt.map { it.testTable }, tableJoiner)
                }
                val mainModule = MultiModelGluer().apply {
                    val pn = gtts.first().programRuns.first() // only one run in geteta
                    addProgramRun(pn, modCode)
                    addTable("_" + smv.tableModule.name, smv.ttType!!)
                }
                val m = arrayListOf(mainModule.product, modCode, smv.tableModule)
                m.addAll(smv.helperModules)
                m
            } else {
                info("Constructing final SMV file.")
                val modTable = tt.map { it.tableModule }
                val mainModule = MultiModelGluer().apply {
                    val pn = gtts.first().programRuns.first() // only one run in geteta
                    addProgramRun(pn, modCode)
                    tt.forEach {
                        addTable("_" + it.testTable.name, it.ttType!!)
                    }
                }
                val m = arrayListOf(mainModule.product, modCode)
                m.addAll(modTable)
                tt.forEach { m.addAll(it.helperModules) }
                m
            }

        val t = this.tableOptions.table.first()
        val folder = File(t.parent, t.nameWithoutExtension).absolutePath
        val verificationTechnique = gtts.first().options.verificationTechnique
        info("Run nuXmv: $nuxmv in $folder using ${verificationTechnique}")
        val nuxmv = findProgram(nuxmv)

        val process =
            GetetaFacade.createNuXMVProcess(
                folder, modules, nuxmv?.absolutePath ?: "n/a",
                verificationTechnique
            )

        if (dryRun) {
            if (nuxmv == null) {
                error("Could not find ${this.nuxmv}.")
                exitProcess(1)
            }

            val b = process.call()
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
                if (cexAnalysation.cexPrinter) {
                    useCounterExamplePrinter(outputFolder, b, tt, lineMap, code)
                    useCounterExamplePrinterHtml(outputFolder, b, tt, lineMap, code)
                } else info("Use `--cexout' to print a cex analysation.")

                if (cexAnalysation.cexJson) useCounterExamplePrinterJson(outputFolder, b, tt)
                else info("Use `--cexjson' to print a cex analysation as json.")

                if (cexAnalysation.runAnalyzer) createRowMapping(b, tt)
                else info("Use `--row-map' to print possible row mappings.")
            }
            info("STATUS: $status")
            exitProcess(errorLevel)
        } else {
            info("Model checker skipped due to `--dont-model-check` flag.")
        }
    }

    private fun useCounterExamplePrinterJson(
        outputFolder: String,
        result: NuXMVOutput.Cex,
        tt: List<SMVConstructionModel>
    ) {
        for (model in tt) {
            val file = File(outputFolder, "cex_${model.testTable.name}.json")
            info("Writing JSON counter example to $file")
            val cep = CounterExamplePrinterJson(
                automaton = model.automaton,
                testTable = model.testTable,
                cex = result.counterExample
            )
            file.writeText(cep.call())
        }
    }

    private fun drawAutomaton(gtt: List<GeneralizedTestTable>, tt: TestTableAutomaton) {
        val ad = AutomatonDrawer(
            File(outputFolder, "${gtt.first().name}.dot"),
            gtt.map { it.region }, tt
        )
        ad.runDot = true
        ad.show = automataOptions.showAutomaton
        ad.run()
        if (automataOptions.showAutomaton) {
        }
        info("Image viewer should open now")
    }

    private fun drawAutomaton(gtt: GeneralizedTestTable, tt: SMVConstructionModel) {
        val ad = AutomatonDrawer(
            File(outputFolder, "${gtt.name}.dot"),
            listOf(gtt.region), tt.automaton
        )
        ad.runDot = true
        ad.show = automataOptions.showAutomaton
        ad.run()
        if (automataOptions.showAutomaton) {
        }
        info("Image viewer should open now")
    }

    private fun createRowMapping(result: NuXMVOutput.Cex, tt: List<SMVConstructionModel>) {
        val mappings = tt.map {
            GetetaFacade.analyzeCounterExample(
                it.automaton, it.testTable, result.counterExample
            )
        }

        mappings.zip(tt).forEach { (m, tt) ->
            m.forEachIndexed { i, m ->
                val a = m.asRowList().joinToString(", ", "[", "]")
                info("Mapping ${tt.testTable.name}#$i:\t$a")
            }
        }

        when {
            mappings.isEmpty() -> warn("no row mapping found!")
            cexAnalysation.odsExport == null -> info("Use `--ods <table.ods>' to generate a counterexample tables.")
            cexAnalysation.odsExport != null -> {
                val w = ODSCounterExampleWriter(result.counterExample)
                tt.zip(mappings).forEach { (t, m) ->
                    w.addTestTable(t, m)
                }
                w.run()
                w.writer.saveAs(cexAnalysation.odsExport)
                FastOds.openFile(cexAnalysation.odsExport)
            }
        }
    }
}

internal fun List<GeneralizedTestTable>.filterByName(tableWhitelist: List<String>): List<GeneralizedTestTable> =
    if (tableWhitelist.isNotEmpty())
        this.filter { it.name in tableWhitelist }
    else
        this


fun useCounterExamplePrinter(
    outputFolder: String?, result: NuXMVOutput.Cex, tt: List<SMVConstructionModel>,
    lineMap: LineMap, program: PouExecutable
) {
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
                stream = stream
            )
            cep.getAll()
        }
    }
}


fun useCounterExamplePrinterHtml(
    outputFolder: String?, result: NuXMVOutput.Cex, tt: List<SMVConstructionModel>,
    lineMap: LineMap, program: PouExecutable
) {
    for (model in tt) {
        for (k in 0 until result.counterExample.stateSize - 1) {
            val name = "cex_${model.testTable.name}"
            val file = File("$outputFolder/cex", "$name.$k.html")
            file.parentFile.mkdirs()
            file.bufferedWriter().use {
                val cep = CounterExamplePrinterWithProgramHtml(
                    automaton = model.automaton,
                    testTable = model.testTable,
                    cex = result.counterExample,
                    lineMap = lineMap,
                    program = program,
                    stream = it,
                    name = name
                )
                cep.print(k)
            }
        }
    }
}


object GetetaSmt {
    @JvmStatic
    fun main(args: Array<String>) = GetetaSmtApp().main(args)
}

class GetetaSmtApp : CliktCommand() {
    val programOptions by ProgramOptions()
    val tableOptions by TableArguments()
    val outputFolder by outputFolder()

    override fun run() {
        SCOPE_SEPARATOR = "___"

        //region read table
        val tables = tableOptions.table.flatMap {
            info("Use table file ${it.absolutePath}")
            GetetaFacade.readTables(it)
        }.map {
            it.programRuns = listOf("")
            it.generateSmvExpression()
            it.simplify()
        }.filterByName(tableOptions.tableWhitelist)


        //endregion
        info("Tables found: ${tables.joinToString()}")

        //region read program
        val (pous, exec) = IEC61131Facade.readProgramWLNP(
            programOptions.library, programOptions.program.first()
        )
        require(pous.isNotEmpty()) { "No program was given" }
        require(exec != null) { "Could not find any program by ${pous.first()}" }
        //endregion

        val enum = exec.scope.enumValuesToType()

        for (table in tables) {
            info("Compute miter and product program for table ${table.name}")
            val automaton = GetetaFacade.constructTable(table)
            val mc = GttMiterConstruction(table, automaton.automaton, enum)
            val miter = mc.constructMiter()
            val program = ProgMiterConstruction(pous).constructMiter()

            val productProgramBuilder = InvocationBasedProductProgramBuilder()
            productProgramBuilder.add(program)
            productProgramBuilder.add(miter)
            val productProgram = productProgramBuilder.build(false)

            val outputFile = File(outputFolder ?: ".", table.name + ".hcc").absoluteFile
            outputFile.bufferedWriter().use { out ->
                val simplifiedProductProgram = SymbExFacade.simplify(productProgram)
                val hccprinter = HccPrinter(CodeWriter(out))
                hccprinter.isPrintComments = true
                productProgramBuilder.target.functions.forEach {
                    it.accept(hccprinter)
                }
                simplifiedProductProgram.accept(hccprinter)
            }
            info("File: $outputFile written")
        }
    }
}