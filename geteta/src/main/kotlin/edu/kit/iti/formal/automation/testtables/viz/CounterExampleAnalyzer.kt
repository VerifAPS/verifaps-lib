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

import edu.kit.iti.formal.automation.testtables.builder.stateNameSentinel
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.SpecialState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*
import java.util.concurrent.Callable

data class Mapping(private val state2Row: MutableList<Pair<Int, String>> = arrayListOf()) {
    constructor(sz: Int) : this(ArrayList(sz))

    fun asRowList() = state2Row.sortedBy { it.first }.map { it.second }
    fun connect(state: Int, row: String) = state2Row.add(state to row)
    fun row(state: Int) = state2Row.find { (s, _) -> state == s }?.second
    fun state(row: String) = state2Row.find { (_, r) -> row == r }?.first
}

private data class SearchNode(
    val cycle: Int,
    val state: AutomatonState,
    val parent: SearchNode? = null,
) {

    fun jumpTo(to: AutomatonState): SearchNode = SearchNode(cycle + 1, to, this)

    val searchPath: List<SearchNode>
        get() {
            return if (parent == null) {
                listOf(this)
            } else {
                parent.searchPath + this
            }
        }

    val mapping: Mapping
        get() {
            val sp = searchPath
            val m = Mapping(sp.size)
            searchPath.forEachIndexed { i, it ->
                if (it.state is RowState) {
                    m.connect(i, it.state.row.id)
                }
            }
            return m
        }
}

class CounterExamplePrinterJson(
    val automaton: TestTableAutomaton,
    val testTable: GeneralizedTestTable,
    val cex: CounterExample,
) : Callable<String> {

    override fun call(): String = (0 until cex.stateSize - 1).joinToString(", ", "[", "]") {
        getTableVars(it)
    }

    val tableRows = testTable.region.flat()
    val prfx = "_${testTable.name}."

    private fun getTableVars(k: Int) = tableRows.joinToString(", ", "[", "]") { row ->
        val activateStates = isRowActive(k, row)
        val rowActive = activateStates.isNotEmpty()
        val assumption = prfx + row.defInput.name
        val assertion = prfx + row.defOutput.name
        val fwd = prfx + row.defForward.name
        val failed = prfx + row.defFailed.name

        val times =
            if (activateStates.isEmpty()) {
                "[]"
            } else {
                activateStates.joinToString(", ", "[", "]") { it.toString() }
            }

        appendJSONObject(
            "rowId" to "\"${row.id}\"",
            "active" to rowActive,
            "assumption" to boolForHuman(k, assumption),
            "assertion" to boolForHuman(k, assertion),
            "accept" to boolForHuman(k, fwd),
            "fail" to boolForHuman(k, failed),
            "time" to times,
            "cells" to getFields(row, k),
        )
    }

    private fun getFields(row: TableRow, k: Int): Any? {
        fun name(v: SVariable, k: String) = "${prfx}${v.name}_$k"
        fun names(v: SVariable, ks: Iterable<String>) = ks.asSequence().map { it to name(v, it) }
        val defines = names(row.defInput, row.inputExpr.keys) + names(row.defOutput, row.outputExpr.keys)
        return defines.joinToString(", ", "{", "}") { (cell, def) ->
            "\"$cell\": ${boolForHuman(k, def)}"
        }
    }

    private fun boolForHuman(k: Int, n: String): String? {
        val v = cex[k, n]
        return when (v) {
            "TRUE" -> "true"
            "FALSE" -> "false"
            else -> "\"undefined\""
        }
    }

    private fun isRowActive(k: Int, it: TableRow): List<Int> = automaton.getStates(it)
        ?.filter { rs ->
            cex[k, "_${testTable.name}.${rs.name}"] == "TRUE"
        }
        ?.map { it.time }
        ?: listOf()
}

private fun appendJSONObject(vararg pairs: Pair<String, Any?>) = pairs.joinToString(", ", "{", "}") { (k, v) ->
    "\"$k\": $v"
}

/**
 * @author Alexander Weigl
 * @version 1 (08.02.17)
 */
class CounterExampleAnalyzer(
    val automaton: TestTableAutomaton,
    val testTable: GeneralizedTestTable,
    val counterExample: CounterExample,
    val tableModuleName: String,
) {

    private val tableRows = testTable.region.flat()
    val rowMapping: MutableList<Mapping> = arrayListOf()

    fun run() {
        val init = tableRows.filter { it.isInitialReachable }
            .map { automaton.getFirstState(it) as RowState }
            .map { SearchNode(0, it) }

        val queue = LinkedList(init)

        while (!queue.isEmpty()) {
            val cur = queue.remove()
            val (cycle, row, _) = cur

            // only consider rows.
            if (row is SpecialState) {
                if (testTable.options.mode == Mode.CONCRETE_TABLE && row.name == stateNameSentinel) {
                    rowMapping.add(cur.mapping)
                }
                continue
            }

            // traces ended nowhere, but sometimes it happens that the last is not fully complete printed
            // bad for concretization
            if (cycle >= counterExample.stateSize) {
                if (testTable.options.mode == Mode.CONCRETE_TABLE) {
                    rowMapping.add(cur.mapping)
                }
                continue
            }

            // Smart casting
            if (row !is RowState) continue

            if (getBoolean(cycle, row.fwd)) {
                // include every outgoing tableRow
                automaton.transitions.filter { it.from == row }
                    .forEach { queue.add(cur.jumpTo(it.to)) } // TODO exclude error?
            }

            val failed =
                when {
                    testTable.options.mode == Mode.CONCRETE_TABLE ->
                        getBoolean(cycle, stateNameSentinel)

                    else ->
                        getBoolean(cycle, row.fail)
                }
            if (failed) {
                // yuhuuu the counter example
                rowMapping.add(cur.mapping)
            }
        }
    }

    private fun getBoolean(time: Int, `var`: String): Boolean = "TRUE" == getValue(time, `var`)

    private fun getValue(time: Int, variable: String): String? {
        val v = "$tableModuleName.$variable"
        return counterExample[time, v]
    }
}
