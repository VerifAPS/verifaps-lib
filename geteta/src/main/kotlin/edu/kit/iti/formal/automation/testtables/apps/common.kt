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

import com.github.ajalt.clikt.parameters.groups.OptionGroup
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.util.info

class CexAnalysationArguments : OptionGroup() {
    val cexJson by option("--cexjson", help = "exports an analysis of the counter example in json").flag()

    val runAnalyzer by option("--row-map", help = "print out a mapping between table rows and states")
        .flag("--no-row-map", default = false)

    val odsExport by option("--ods", help = "generate ods counter-example file").file()
    val odsOpen by option("--ods-open").flag()

    val cexPrinter by option("--cexout", help = "prints an analyis of the counter example and the program")
        .flag()
}

class AutomataOptions : OptionGroup() {
    val drawAutomaton by option(
        "--debug-automaton",
        help = "generate a dot file, showing the generated automaton",
    ).flag(default = false)
    val showAutomaton by option(
        "--show-automaton",
        help = "run dot and show the image of the automaton",
    ).flag(default = false)
}

class TableArguments : OptionGroup() {
    fun readTables(): List<GeneralizedTestTable> = table.flatMap {
        info("Use table file ${it.absolutePath}")
        info("Time constants: $timeConstants")
        GetetaFacade.readTables(it, timeConstants)
    }.map {
        it.ensureProgramRuns()
        it.generateSmvExpression()
        it.simplify()
    }.filterByName(tableWhitelist)

    val timeConstants: Map<String, Int> by option("-T", help = "setting a time constant")
        .splitPair("=")
        .convert { it.first to it.second.toInt() }
        .multiple()
        .toMap()

    val table by option("-t", "--table", help = "test table file", metavar = "FILE")
        .file(mustExist = true, mustBeReadable = true)
        .multiple(required = true)
    val tableWhitelist by option(
        "--select-table",
        metavar = "TABLE_NAME",
        help = "specify table by name, which should be used from the given file",
    )
        .multiple()
    val enableMesh by option("--meshed", help = "enable experimental meshed tables")
        .flag("-M", default = false)
}