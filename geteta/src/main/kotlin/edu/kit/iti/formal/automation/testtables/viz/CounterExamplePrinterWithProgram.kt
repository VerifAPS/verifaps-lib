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

import edu.kit.iti.formal.automation.VisualizeTrace
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.util.CodeWriter

class CounterExamplePrinterWithProgram(
    val automaton: TestTableAutomaton,
    val testTable: GeneralizedTestTable,
    val cex: CounterExample,
    lineMap: LineMap,
    val program: PouExecutable,
    val stream: CodeWriter = CodeWriter(),
) {

    val vt = VisualizeTrace(cex, lineMap, program, stream).also { vt ->
        vt.programVariableToSVar = { "code$.$it" }
    }

    fun getAll() {
        for (k in 0 until cex.stateSize - 1) {
            get(k)
        }
    }

    fun get(k: Int) {
        vt.get(k, k + 1)
        printAssertions(k)
    }

    private fun printAssertions(k: Int) {
        stream.print(" * Table rows:").nl()
        printVariables(k)
    }

    private fun printVariables(k: Int) {
        testTable.region.flat()
            .forEach { row ->
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
            }
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