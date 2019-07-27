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
package edu.kit.iti.formal.automation.testtables.viz

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.testtables.builder.stateNameSentinel
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.SpecialState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import edu.kit.iti.formal.smv.CounterExample
import java.util.*

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
        val parent: SearchNode? = null) {

    fun jumpTo(to: AutomatonState): SearchNode = SearchNode(cycle + 1, to, this)

    val searchPath: List<SearchNode>
        get() {
            return if (parent == null) listOf(this)
            else parent.searchPath + this
        }

    val mapping: Mapping
        get() {
            val sp = searchPath
            val m = Mapping(sp.size)
            searchPath.forEachIndexed { i, it ->
                if (it.state is RowState)
                    m.connect(i, it.state.row.id)
            }
            return m
        }
}

/**
 * @author Alexander Weigl
 * @version 1 (08.02.17)
 */
class CounterExampleAnalyzer(
        val automaton: TestTableAutomaton,
        val testTable: GeneralizedTestTable,
        val counterExample: CounterExample,
        val tableModuleName: String) {

    private val tableRows = testTable.region.flat()
    val rowMapping: MutableList<Mapping> = arrayListOf()

    fun run() {
        val init = tableRows.filter { it.isInitialReachable }
                .map { automaton.getFirstState(it) as RowState }
                .map { SearchNode(0, it) }

        val queue = LinkedList<SearchNode>(init)

        while (!queue.isEmpty()) {
            val cur = queue.remove()
            val (cycle, row, _) = cur

            // only consider rows.
            if (row is SpecialState) {
                if (testTable.options.mode == Mode.CONCRETE_TABLE && row.name == stateNameSentinel)
                    rowMapping.add(cur.mapping)
                continue
            }

            // traces ended nowhere, but sometimes it happens that the last is not fully complete printed
            // bad for concretization
            if (cycle >= counterExample.stateSize) {
                if (testTable.options.mode == Mode.CONCRETE_TABLE)
                    rowMapping.add(cur.mapping)
                continue
            }

            //Smart casting
            if (row !is RowState) continue

            if (getBoolean(cycle, row.fwd)) {
                //include every outgoing tableRow
                automaton.transitions.filter { it.from == row }
                        .forEach { queue.add(cur.jumpTo(it.to)) }
            }

            val failed =
                    when {
                        testTable.options.mode == Mode.CONCRETE_TABLE ->
                            getBoolean(cycle, stateNameSentinel)
                        else ->
                            getBoolean(cycle, row.fail)
                    }
            if (failed) {
                //yuhuuu the counter example
                rowMapping.add(cur.mapping)
            }
        }
    }

    private fun getBoolean(time: Int, `var`: String): Boolean {
        return "TRUE" == getValue(time, `var`)
    }

    private fun getValue(time: Int, variable: String): String? {
        val v = tableModuleName + "." + variable
        return counterExample[time, v]
    }
}
