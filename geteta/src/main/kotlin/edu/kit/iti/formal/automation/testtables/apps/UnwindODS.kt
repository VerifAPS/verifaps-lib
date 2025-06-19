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
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.viz.DefaultTableStyle
import edu.kit.iti.formal.automation.testtables.viz.TableUnwinder
import edu.kit.iti.formal.automation.testtables.viz.createTableWithProgram
import edu.kit.iti.formal.automation.testtables.viz.createTableWithoutProgram
import edu.kit.iti.formal.util.info

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

class UnwindODS : CliktCommand(name = "tt-debug.sh") {
    override fun helpEpilog(context: Context) = "UnwindODS -- Tooling for Relational Test Tables."

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
        info("Program: {} ith library {}", program, library)
        val smvModule = if (program != null) {
            IEC61131Facade.readProgramsWLN(library, listOf(program!!), listOf(selector)).first()?.let {
                SymbExFacade.evaluateProgram(it)
            }
        } else {
            null
        }

        info("Program {} found!", if (smvModule != null) "" else "not")

        val gtts = table.flatMap { GetetaFacade.readTables(it) }
            .map {
                it.ensureProgramRuns()
                it.generateSmvExpression()
                it
            }

        gtts.forEach { gtt ->
            val unwinded = TableUnwinder(gtt, HashMap())() // use default
            info("Unwinded tabe contains {} rows", unwinded.size)
            gtt.constraintVariables.forEach {
                info(
                    "You need to define a cell for {} : {}, manually",
                    it.name,
                    it.dataType.name,
                )
            }

            val table =
                if (smvModule != null) {
                    createTableWithProgram(smvModule, gtt, DefaultTableStyle, unwinded)
                } else {
                    createTableWithoutProgram(gtt, DefaultTableStyle, unwinded)
                }

            table.run()
            table.writer.saveAs(outputFile)
            info("Table written to {}", outputFile.absolutePath)
        }
    }
}