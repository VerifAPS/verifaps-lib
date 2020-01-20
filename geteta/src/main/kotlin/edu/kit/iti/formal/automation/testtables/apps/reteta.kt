package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
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
import edu.kit.iti.formal.util.*
import java.io.File
import java.util.*
import kotlin.error
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

    val verbose by option("--verbose", "-v", help = "verbose output").counted()

    val invokeModelChecker by option("--model-check", help = "the model checker is invoked when set [default:true]")
            .flag("--dont-model-check", default = true)

    val printAugmentedPrograms by option(help = "prints the augmented programs into files: <name>.st").flag()

    val disableSimplify by option("--no-simplify", help = "disable")
            .flag(default = false)

    val table by option("-t", "--table", help = "the xml file of the table", metavar = "FILE")
            .file()
            .multiple(required = true)

    val outputFolder by option("-o", "--output", help = "Output directory")
            .defaultLazy { table.first().nameWithoutExtension }

    val library by option("-L", "--lib", help = "program files")
            .convert { File(it) }
            .multiple()

    val verificationTechnique by option("--technique",
            help = "verification technique")

    val programs by option("-P", "--program", metavar = "NAME")
            //.convert { File(it) }
            .multiple(required = true)

    val nuxmv by option("--nuxmv", help = "Path to nuXmv binary.", envvar = "NUXMV")
            .file(exists = true)

    val drawAutomaton by option("--debug-automaton").flag(default = false)
    val showAutomaton by option("--show-automaton").flag(default = false)

    override fun run() {
        currentDebugLevel = verbose

        if (table.isEmpty() || programs.isEmpty()) {
            fail("No code or table file given.")
        }
        //read program
        val programs = readPrograms()


        val superEnumType = GetetaFacade.createSuperEnum(programs.map { it.scope })

        /*val programRunNames = programs.mapIndexed { index, it ->
            "${it.name.toLowerCase()}$$index"
        }*/

        //read table
        val gtts = table.flatMap { GetetaFacade.readTables(it) }.map {
            it.simplify()
        }

        gtts.forEach { table ->
            val chapterMarks = table.chapterMarksForProgramRuns
            val augmentedPrograms = programs.mapIndexed { idx, exec ->
                val rttPipeline = RTTCodeAugmentation(chapterMarks[idx]!!)
                val s = rttPipeline.transform(TransformationState(exec))
                val p = ProgramDeclaration(exec.name, s.scope, s.stBody)

                if (printAugmentedPrograms) {
                    File(outputFolder).mkdirs()
                    val out = File(outputFolder, "${exec.name}.st")
                    out.bufferedWriter().use {
                        IEC61131Facade.printTo(it, p)
                    }
                    info("Write augmented program into $out.")
                }

                SymbExFacade.evaluateProgram(p, disableSimplify)
            }

            if (!table.options.relational) {
                throw IllegalStateException()
            }


            val tt = GetetaFacade.constructSMV(table, superEnumType)

            if (drawAutomaton) {
                info("Automaton drawing requested. This may took a while.")
                val ad = AutomatonDrawer(File(outputFolder, "${table.name}.dot"), table, tt.automaton)
                ad.runDot = true
                ad.show = showAutomaton
                ad.run()
                if (showAutomaton)
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
                    outputFolder, modules, nuxmv?.absolutePath ?: "nuxmv",
                    table.options.verificationTechnique)
            if (invokeModelChecker) {
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
        info("Provided library code: $library")
        info("Reading programs (in order): $programs")
        val programs = IEC61131Facade.readProgramsWLPN(library, programs)
        val nullIndex = programs.indexOf(null)
        if (nullIndex >= 0) {
            fail("Could not find an executable pou in '${this.programs[nullIndex]}'.")
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