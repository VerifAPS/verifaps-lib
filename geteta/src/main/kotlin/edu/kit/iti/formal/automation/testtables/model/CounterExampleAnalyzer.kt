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
package edu.kit.iti.formal.automation.testtables.model

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

import edu.kit.iti.formal.automation.testtables.report.Message
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (08.02.17)
 */
class CounterExampleAnalyzer(testTable: GeneralizedTestTable, private val message: Message) {
    private val states: List<State>
    private val ceStates = ArrayList<Map<String, String>>()
    private val ceInput = ArrayList<Map<String, String>>()

    init {
        this.states = testTable.region!!.flat()

        //making a dense counter example
        var lastState: Map<String, String> = HashMap()
        var lastInput: Map<String, String> = HashMap()
        for (step in message.counterexample.trace
                .step) {
            val state = HashMap(lastState)
            val input = HashMap(lastInput)

            step.input.forEach { a -> input[a.name] = a.value }

            step.state.forEach { a -> state[a.name] = a.value }

            lastState = state
            lastInput = input

            ceInput.add(input)
            ceStates.add(state)
        }

        val value = Message.Counterexample.RowMappings()
        message.counterexample.rowMappings = value
    }

    fun run(): List<String> {
        val queue = LinkedList<SearchNode>()
        for (s in this.states) {
            for (a in s.automataStates) {
                if (a.isStartState && isTrue(0, a.smvVariable)) {
                    val sn = SearchNode(0, a)
                    queue.add(sn)
                } else {
                    break
                }
            }
        }

        while (!queue.isEmpty()) {
            val cur = queue.remove()
            val time = cur.time
            val state = cur.state

            if (time >= ceStates.size)
                continue

            val fwd = state.defForward.name
            val failed = state.defFailed.name

            if (isTrue(time, fwd)) {
                //include every outgoing state
                state.outgoing.forEach { r -> queue.add(SearchNode(time + 1, r, cur)) }

                //step can be repeated infinitely, if fwd=TRUE
                if (state.isUnbounded && isTrue(time, fwd)) {
                    queue.add(SearchNode(time + 1, state, cur))
                }
            }

            if (isTrue(time, failed)) {
                //yuhuuu the counter example
                message.counterexample.rowMappings.rowMap
                        .add(cur.rows)
            }
        }
        return message.counterexample.rowMappings.rowMap
    }

    private fun isTrue(time: Int, `var`: SVariable): Boolean {
        return isTrue(time, `var`.name)
    }

    private fun isTrue(time: Int, `var`: String): Boolean {
        return "TRUE" == getValue(time, `var`)
    }

    private fun getValue(time: Int, variable: String): String? {
        var _var = variable
        _var = "table." + variable
        try {
            val `val` = ceInput[time][_var]
            if (`val` != null)
                return `val`
        } catch (e: IndexOutOfBoundsException) {

        }

        try {
            return ceStates[time][_var]
        } catch (e1: IndexOutOfBoundsException) {
        }

        return null
    }

    private fun isFalse(time: Int, `var`: String): Boolean {
        return "FALSE" == getValue(time, `var`)
    }

    private class SearchNode(internal val time: Int, internal val state: State.AutomatonState,
                             internal val parent: SearchNode?) {

        val rows: String
            get() {
                var s = ""
                if (parent != null)
                    s = parent.rows + ", "
                return s + state.state.id!!
            }

        constructor(i: Int, s: State.AutomatonState) : this(i, s, null) {}
    }
}
