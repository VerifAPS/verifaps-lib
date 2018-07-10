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
package edu.kit.iti.formal.automation.testtables.algorithms


import edu.kit.iti.formal.automation.testtables.builder.ConstructionModel
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.Region
import edu.kit.iti.formal.automation.testtables.model.State
import java.util.*
import kotlin.collections.ArrayList

/**
 * Calculation of the State/Row reachability.
 *
 *
 * A *i*th row can reach (directly) the *j*th row iff
 *
 *
 *  1. *(i+1)*th can reach the *j*th row and the duration
 * of *i+1* can be zero ([edu.kit.iti.formal.automation.testtables.model.Duration].getLower() == 0).
 *
 *  1.
 * *i*th row is the end of block and *j*th row is the beginning of the same block.
 *
 *
 *
 *
 * This resolution is programmed as a fixpoint algorithm.
 *
 *
 *
 * Currently supports of blocks and arbitrary durations.
 *
 *
 * @author Alexander Weigl
 * @version 2 (12.12.16)
 */
class StateReachability(
        private val sentinel: State,
        root: Region) {

    private val flatList: MutableList<State>

    constructor(model: ConstructionModel) :
            this(model.sentinelState, model.testTable.region)

    init {
        sentinel.duration = Duration.ClosedInterval(1, 1)
        flatList = ArrayList(root.flat())
        val lastState = flatList[flatList.size - 1]

        if (lastState.duration !== edu.kit.iti.formal.automation.testtables.model.Duration.Omega) {
            flatList.add(sentinel)
        }

        initTable()
        addRegions(root)
        fixpoint()
        maintainIncomning()
        maintainAutomata()
        isInitialReachable()
    }

    private fun maintainAutomata() {
        for (state in flatList) {
            val astates = state.automataStates
            for (i in astates.indices) {
                val a = astates[i]

                if (a.isFirst) {
                    val s = a.state
                    s.incoming
                            .flatMap { it.automataStates }
                            .filter { it.isOptional }
                            .forEach { b -> connect(b, a) }
                }

                //
                if (i + 1 < astates.size) {
                    connect(a, astates[i + 1])
                }

                //connect to first automata state in every next row
                if (a.isOptional) {
                    state.outgoing.forEach { next -> connect(a, next.automataStates[0]) }
                }

                if (a.isUnbounded) {
                    connect(a, a)
                }
            }
            state.isEndState = state.outgoing.contains(sentinel)
        }
    }

    private fun connect(a: State.AutomatonState, b: State.AutomatonState) {
        a.outgoing.add(b)
        b.incoming.add(a)
    }

    private fun maintainIncomning() {
        for (out in flatList) {
            for (`in` in out.outgoing) {
                `in`.incoming.add(out)
            }
        }
    }

    /**
     * The fixpoint algorithm.
     * Needs to be initialize with the direct reachable of i to i+1 and the region borders.
     */
    private fun fixpoint() {
        var changed = true
        while (changed) { // as long we have changes
            changed = false
            //for each row
            for (state in flatList) {
                val oldSize = state.outgoing.size
                val reached = HashSet<State>(flatList.size)
                //foreach reachable state
                for (reachable in state.outgoing) {
                    // if reachable state is isSkippable, add their reachable state list
                    if (reachable.duration.isSkippable) {
                        reached.addAll(reachable.outgoing)
                    }
                }
                //add to the outgoing
                state.outgoing.addAll(reached)
                //check for size
                changed = changed || state.outgoing.size != oldSize
            }
        }
    }

    /**
     * initialize the region borders
     *
     * @param r
     */
    private fun addRegions(r: Region) {
        if (r.duration.isRepeatable) {
            val flat = r.flat()
            flat[r.children.size - 1].outgoing
                    .add(flat[0])
        }

        //Regions can be isSkippable
        r.children.forEach {
            if (it is Region) addRegions(it)
        }
    }

    /**
     * Initialize the table with the direct reachability.
     * 1. i-th row can reach (i+1)-th row
     * 2. End of the region, to beginning of a region.
     * 3. Abort on \omega!
     */
    private fun initTable() {
        for (i in 0 until flatList.size - 1) {
            if (flatList[i].duration === Duration.Omega) {
                break
            }
            flatList[i].outgoing.add(flatList[i + 1])
        }
    }

    private fun isInitialReachable() {
        val queue = LinkedList<State>()
        queue.add(flatList[0])
        while (!queue.isEmpty()) {
            val s = queue.remove()
            //already reached
            if (s.isInitialReachable)
                continue

            s.isInitialReachable = true

            if (s.duration.isSkippable)
                queue.addAll(s.outgoing)
        }
    }
}