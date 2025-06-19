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
package edu.kit.iti.formal.automation.testtables.model.automata

import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.smv.ast.SMVExpr

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
data class Transition(val name: String, val from: AutomatonState, val to: AutomatonState, var type: TransitionType)

enum class TransitionType {
    ACCEPT,
    ACCEPT_PROGRESS,
    FAIL,
    TRUE,
    MISS,
}

sealed class AutomatonState(open var name: String) {
    var optional: Boolean = false
    var progressFlag: Boolean = false
    var strongRepetition: Boolean = false
    var weakRepeat: Boolean = false
}

data class SpecialState(override var name: String) : AutomatonState(name)
data class RowState(val row: TableRow, val time: Int) : AutomatonState("%s_%02d".format(row.id, time)) {
    val miss = "${name}_miss"
    val fwd = "${name}_accept"
    val fwdprogress = "${name}_acceptp"
    val fail = "${name}_fail"
}

/*
class AutomatonState(private val position: Int, private val name: String) {
    val incoming: MutableSet<AutomatonState> = java.util.HashSet()
    val outgoing: MutableSet<AutomatonState> = java.util.HashSet()

    constructor(count: Int) : this(count, "${TableRow@ id}_$id")

    val isOptional: Boolean
        get() {
            val duration = duration
            return when (duration) {
                is Duration.Omega -> false
                is Duration.ClosedInterval -> position >= duration.lower
                is Duration.OpenInterval -> position >= duration.lower
            }
        }

    val isFirst: Boolean
        get() = position == 1

    val state: edu.kit.iti.formal.automation.testtables.model.TableRow
        get() = this@TableRow

    val smvVariable: SVariable = SVariable.create("s_$name").asBool()

    val defForward: SVariable = SVariable.create("s_${name}_fwd").asBool()

    val defFailed: SVariable = SVariable.create("s_${name}_fail").asBool()

    /**
 * Returns true iff this is the automaton state that can infinitely repeated.
 *
 * @return
 */
    val isUnbounded: Boolean
        get() {
            val duration = duration
            return when (duration) {
                is Duration.Omega -> true
                is Duration.ClosedInterval -> false
                is Duration.OpenInterval -> position == duration.lower
            }
        }

    val isStartState: Boolean
        get() = isInitialReachable && isFirst

    val isEndState: Boolean
        get() = if (outgoing.isEmpty()) {
            true //TODO check for omega?
        } else {
            outgoing.stream()
                    .map { s -> s.isEndState || s.isOptional }
                    .reduce { a, b -> a or b }.orElse(false)
        }
}*/

data class TestTableAutomaton(
    val rowStates: MutableMap<TableRow, List<RowState>> = HashMap(),
    val transitions: MutableList<Transition> = ArrayList(),
) {
    var definitions: MutableMap<String, SMVExpr> = HashMap()
    var stateError: AutomatonState = SpecialState("n/a")
    var stateSentinel: AutomatonState = SpecialState("n/a")
    val initialStates: MutableSet<AutomatonState> = HashSet()

    fun addTransition(from: AutomatonState, to: AutomatonState, guard: TransitionType) {
        val name = ""
        transitions.add(Transition(name, from, to, guard))
    }

    fun getTransition(from: AutomatonState, to: AutomatonState): Transition? = transitions.find {
        it.from == from &&
            it.to == to
    }

    fun clear() {
        transitions.clear()
        rowStates.clear()
        initialStates.clear()
    }

    fun getStates(s: TableRow) = rowStates[s]
    fun getFirstState(s: TableRow) = getState(s, 0)
    fun getState(s: TableRow, cycle: Int) = rowStates[s]?.get(cycle)

    fun getRowStates(): Sequence<RowState> = rowStates.asSequence().flatMap { it.value.asSequence() }

    fun getStartStates(): List<RowState> = rowStates
        .filter { (k, _) -> k.isInitialReachable }
        .map { (_, v) -> v.get(0) }

    fun getOutgoingTransition(from: AutomatonState) = transitions.filter { it.from == from }

    fun getIncomingTransition(to: AutomatonState) = transitions.filter { it.to == to }
}