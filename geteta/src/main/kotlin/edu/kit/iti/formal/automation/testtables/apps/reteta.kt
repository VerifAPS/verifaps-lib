package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
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

class Reteta : CliktCommand(
        epilog = "Reteta -- Tooling for Relational Test Tables.",
        name = "reteta") {

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

        //read program
        val programs = readPrograms()
        val superEnumType = GetetaFacade.createSuperEnum(programs.map { it.scope })

        //read table
        val gtts = tableOptions.table.flatMap { GetetaFacade.readTables(it) }.map {
            it.simplify()
        }

        gtts.forEach { table ->
            val chapterMarks = table.chapterMarksForProgramRuns
            val augmentedPrograms = programs.mapIndexed { idx, exec ->
                val rttPipeline = RTTCodeAugmentation(false, chapterMarks[idx]!!)
                val s = rttPipeline.transform(TransformationState(exec))
                val p = ProgramDeclaration(exec.name, s.scope, s.stBody)

                if (printAugmentedPrograms) {
                    File(outputFolder).mkdirs()
                    val out = File(outputFolder, "${exec.name}_${idx}.st")
                    out.bufferedWriter().use {
                        IEC61131Facade.printTo(it, p)
                    }
                    info("Write augmented program into $out.")
                }

                SymbExFacade.evaluateProgram(p, true).also {
                    it.name = "${it.name}_${idx}" // rename module, otherwise clash on self-compositions
                }
            }

            if (!table.options.relational) {
                throw IllegalStateException()
            }


            val tt = GetetaFacade.constructSMV(table, superEnumType)

            if (automatonOptions.drawAutomaton) {
                info("Automaton drawing requested. This may took a while.")
                val ad = AutomatonDrawer(File(outputFolder, "${table.name}.dot"),
                        listOf(table.region), tt.automaton)
                ad.runDot = true
                ad.show = automatonOptions.showAutomaton
                ad.run()
                if (automatonOptions.showAutomaton)
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
                    outputFolder, modules, nuxmv,
                    table.options.verificationTechnique)
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