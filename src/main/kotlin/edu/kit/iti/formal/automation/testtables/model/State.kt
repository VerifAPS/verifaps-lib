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


import edu.kit.iti.formal.automation.testtables.schema.IoVariable
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVType
import edu.kit.iti.formal.smv.ast.SVariable
import lombok.Data

import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (10.12.16)
 */
@Data
class State(id: String) : TableNode(id) {
    val inputExpr: List<SMVExpr> = ArrayList()
    val outputExpr: List<SMVExpr> = ArrayList()
    val entryForColumn: Map<String, String> = HashMap()
    val incoming: Set<State> = HashSet()
    val outgoing: Set<State> = HashSet()
    /**
     *
     */
    val defInput: SVariable
    /**
     *
     */
    val defFailed: SVariable
    /**
     *
     */
    val defForward: SVariable
    /**
     *
     */
    val defOutput: SVariable
    /**
     * The predicate that allows keeping in this state.
     * Only necessary iff duration is DET_WAIT.
     */
    val defKeep: SVariable
    private var automataStates: MutableList<AutomatonState>? = null
    var isInitialReachable: Boolean = false
        set(initialReachable) {
            field = isInitialReachable
        }
    var isEndState: Boolean = false
        set(endState) {
            field = isEndState
        }

    override val isLeaf: Boolean
        get() = true

    override val children: List<TableNode>
        get() = Collections.EMPTY_LIST

    init {
        defOutput = SVariable("s" + id + "_out", SMVType.BOOLEAN)
        defForward = SVariable("s" + id + "_fwd", SMVType.BOOLEAN)
        defFailed = SVariable("s" + id + "_fail", SMVType.BOOLEAN)
        defInput = SVariable("s" + id + "_in", SMVType.BOOLEAN)
        defKeep = SVariable("s" + id + "_keep", SMVType.BOOLEAN)
    }

    constructor(id: Int) : this(id.toString()) {}

    fun add(v: IoVariable, e: SMVExpr) {
        val a = if (v.io == "input") inputExpr else outputExpr
        a.add(e)
    }

    override fun count(): Int {
        return 1
    }

    override fun flat(): List<State> {
        val l = LinkedList<State>()
        l.add(this)
        return l
    }

    override fun equals(o: Any?): Boolean {
        if (this === o)
            return true
        if (o == null || javaClass != o.javaClass)
            return false

        val state = o as State?

        return id == state!!.id
    }

    override fun hashCode(): Int {
        return id!!.hashCode()
    }

    override fun getAutomataStates(): List<AutomatonState> {
        if (automataStates == null)
            automataStates = ArrayList()

        if (automataStates!!.size == 0) {
            if (duration.isDeterministicWait || duration.isOmega) {
                automataStates!!.add(AutomatonState(1))
            } else {
                for (i in 1..duration.bound) {
                    automataStates!!.add(AutomatonState(i))
                }
            }
        }
        assert(automataStates!!.size != 0)
        return automataStates
    }


    override fun depth(): Int {
        return 0
    }

    inner class AutomatonState(internal var count: Int) {
        val incoming: Set<AutomatonState> = HashSet()
        val outgoing: Set<AutomatonState> = HashSet()

        val isOptional: Boolean
            get() = count >= duration.lower

        val isFirst: Boolean
            get() = count == 1

        val state: State
            get() = this@State

        val smvVariable: SVariable
            get() = SVariable.create("s_%s_%d", id, count).asBool()

        val defForward: SVariable
            get() = SVariable.create("s_%s_%d_fwd", id, count).asBool()

        val defFailed: SVariable
            get() = SVariable.create("s_%s_%d_fail", id, count).asBool()

        /**
         * Returns true iff this is the automaton state that can infinitely repeated.
         *
         * @return
         */
        val isUnbounded: Boolean
            get() = count == duration.bound && duration.isUnbounded

        val isStartState: Boolean
            get() = isInitialReachable && isFirst

        val isEndState: Boolean
            get() = if (outgoing.size == 0) {
                true
            } else {
                outgoing.stream()
                        .map { s -> s.isEndState || s.isOptional }
                        .reduce { a, b -> a or b }.orElse(false)
            }
    }

    companion object {
        val SENTINEL_ID = "$$$"
    }
}