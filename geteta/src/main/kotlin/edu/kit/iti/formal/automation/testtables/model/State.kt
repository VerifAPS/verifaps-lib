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


import edu.kit.iti.formal.automation.testtables.model.IoVariable
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*
import kotlin.collections.ArrayList

/**
 * @author Alexander Weigl
 * @version 1 (10.12.16)
 */
open class State(id: String) : TableNode(id) {
    /** Input constraints as list. */
    val inputExpr: MutableList<SMVExpr> = ArrayList()
    /** Output constraints as list. */
    val outputExpr: MutableList<SMVExpr> = ArrayList()
    /** Access to the raw fields. */
    val entryForColumn: MutableMap<String, String?> = HashMap()

    /** incoming states */
    val incoming: MutableSet<State> = HashSet()

    /** outgoing states */
    val outgoing: MutableSet<State> = HashSet()

    /** variable of input contraint definition */
    val defOutput = SVariable("s" + id + "_out", SMVTypes.BOOLEAN)
    val defForward = SVariable("s" + id + "_fwd", SMVTypes.BOOLEAN)
    val defFailed = SVariable("s" + id + "_fail", SMVTypes.BOOLEAN)
    val defInput = SVariable("s" + id + "_in", SMVTypes.BOOLEAN)

    /**
     * The predicate that allows keeping in this state.
     * Only necessary iff duration is DET_WAIT.
     */
    val defKeep = SVariable("s" + id + "_keep", SMVTypes.BOOLEAN)


    override val automataStates: MutableList<AutomatonState> = ArrayList()
        get() {
            if (field.isEmpty()) {
                if (duration.isDeterministicWait || duration.isOmega) {
                    field.add(AutomatonState(1))
                } else {
                    for (i in 1..duration.bound) {
                        field.add(AutomatonState(i))
                    }
                }
            }
            assert(field.size != 0)
            return field
        }

    var isInitialReachable: Boolean = false
    var isEndState: Boolean = false

    override val isLeaf: Boolean = true

    override val children: List<TableNode> = Collections.EMPTY_LIST as List<TableNode>

    constructor(id: Int) : this(id.toString())

    fun add(v: IoVariable, e: SMVExpr) {
        val a = if (v.io == IoVariableType.INPUT || v.io == IoVariableType.STATE_INPUT) inputExpr else outputExpr
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


    override fun depth(): Int {
        return 0
    }

    inner class AutomatonState(private val position: Int, private val name: String) {
        val incoming: MutableSet<AutomatonState> = HashSet()
        val outgoing: MutableSet<AutomatonState> = HashSet()

        constructor(count: Int) : this(count, "${State@ id}_$id")

        val isOptional: Boolean
            get() = position >= duration.lower

        val isFirst: Boolean
            get() = position == 1

        val state: State
            get() = this@State

        val smvVariable: SVariable = SVariable.create("s_$name").asBool()

        val defForward: SVariable = SVariable.create("s_${name}_fwd").asBool()

        val defFailed: SVariable = SVariable.create("s_${name}_fail").asBool()

        /**
         * Returns true iff this is the automaton state that can infinitely repeated.
         *
         * @return
         */
        val isUnbounded: Boolean
            get() = position == duration.bound && duration.isUnbounded

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
    }
}