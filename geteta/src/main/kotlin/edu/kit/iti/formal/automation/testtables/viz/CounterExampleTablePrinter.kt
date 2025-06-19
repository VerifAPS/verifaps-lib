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
package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.times

class CounterExampleTablePrinter(
    val automaton: TestTableAutomaton,
    val testTable: GeneralizedTestTable,
    val cex: CounterExample,
    val stream: CodeWriter = CodeWriter(),
) {

    fun print() {
        for (k in 0 until cex.stateSize - 1) get(k)
    }

    fun get(k: Int) {
        printAssertions(k)
    }

    private fun printAssertions(k: Int) {
        val stars = ("*" * 79)
        stream.print("($stars").nl()
        stream.print(" * Table rows:").nl()
        printVariables(k)
        stream.nl().println("$stars)")
    }

    private fun printVariables(k: Int) {
        for (row in testTable.region.flat()) {
            val activateStates = isRowActive(k, row)
            val rowActive = if (activateStates.isNotEmpty()) OKMARK else ERRMARK
            val prfx = "_${testTable.name}."
            val assumption = prfx + row.defInput.name
            val assertion = prfx + row.defOutput.name
            val fwd = prfx + row.defForward.name

            val times = activateStates.joinToString(", ") { it.toString() }

            stream.print(
                " *     $rowActive Row ${row.id} " +
                    "${boolForHuman(k, assumption)} --> ${boolForHuman(k, assertion)}:" +
                    " ${boolForHuman(k, fwd)} (Time: $times)",
            ).nl()

            if (activateStates.isNotEmpty() && !bool(k, assumption)) {
                val violatedAssumpations = testTable.programVariables.filter { it.isAssumption }
                    .map {
                        SVariable(row.defInput.name + "_" + it.name, SMVTypes.BOOLEAN)
                    }
                    .filter { !bool(k, it.name) }
                    .joinToString { it.name }
                stream.print(" *         Violated assumptions: $violatedAssumpations").nl()
            }

            if (activateStates.isNotEmpty() && !bool(k, assertion)) {
                val violatedAssertions = testTable.programVariables.filter { it.isAssertion }
                    .map {
                        prfx + row.defOutput.name + "_" + it.internalVariable(testTable.programRuns).name
                    }
                    .filter { !bool(k, it) }
                    .joinToString { it }
                stream.print(" *         Violated assertions: $violatedAssertions").nl()
            }
        }
    }

    private fun bool(k: Int, n: String) = when (cex[k, n]) {
        "TRUE" -> true
        "FALSE" -> false
        else -> false
    }

    private fun boolForHuman(k: Int, n: String): Char {
        val v = cex[k, n]
        val m = when (v) {
            "TRUE" -> OKMARK
            "FALSE" -> ERRMARK
            else -> QMARK
        }
        return m
    }

    private fun isRowActive(k: Int, it: TableRow): List<Int> = automaton.getStates(it)
        ?.filter { rs ->
            cex[k, "_${testTable.name}.${rs.name}"] == "TRUE"
        }
        ?.map { it.time }
        ?: listOf()
}