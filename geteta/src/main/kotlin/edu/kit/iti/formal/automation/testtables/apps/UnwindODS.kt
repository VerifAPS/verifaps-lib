package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.viz.DefaultTableStyle
import edu.kit.iti.formal.automation.testtables.viz.TableUnwinder
import edu.kit.iti.formal.automation.testtables.viz.createTableWithProgram
import edu.kit.iti.formal.automation.testtables.viz.createTableWithoutProgram

/**
 *
 * @author Alexander Weigl
 * @version 1 (01.10.18)
 */

object UnwindODSApp {
    @JvmStatic
    fun main(args: Array<String>) {
        UnwindODS().main(args)
    }
}

class UnwindODS : CliktCommand(
        epilog = "UnwindODS -- Tooling for Relational Test Tables.",
        name = "tt-debug.sh") {
    val table by argument(help = "the xml file of the table", name = "table")
            .file()
            .multiple()

    val outputFile by option("-o", "--output", help = "Output ODS file")
            .file().required()

    val library by option("-L", "--library", help = "ST code to be weaved in")
            .file().multiple()

    val program by option("-p", "--program", help = "ST code to be weaved in")
            .file()

    val selector: String by option("--name", help = "Name of Program or function block")
            .default("main")

    override fun run() {
        Console.configureLoggingConsole()
        Console.info("Program: {} ith library {}", program, library)
        val smvModule = if (program != null) {
            IEC61131Facade.readProgramsWithLibrary(library, listOf(program!!), selector)[0]?.let {
                SymbExFacade.evaluateProgram(it)
            }
        } else null

        Console.info("Program {} found!", if (smvModule != null) "" else "not")

        val gtts = table.flatMap { GetetaFacade.readTable(it) }
                .map {
                    it.ensureProgramRuns()
                    it.generateSmvExpression()
                    it
                }


        gtts.forEach { gtt->
            val unwinded = TableUnwinder(gtt, HashMap())() //use default
            Console.info("Unwinded tabe contains {} rows", unwinded.size)
            gtt.constraintVariables.forEach {
                Console.info("You need to define a cell for {} : {}, manually",
                        it.name, it.dataType.name)
            }

            val table =
                    if (smvModule != null)
                        createTableWithProgram(smvModule, gtt, DefaultTableStyle, unwinded)
                    else
                        createTableWithoutProgram(gtt, DefaultTableStyle, unwinded)

            table.run()
            table.writer.saveAs(outputFile)
            Console.info("Table written to {}", outputFile.absolutePath)
        }
    }
}