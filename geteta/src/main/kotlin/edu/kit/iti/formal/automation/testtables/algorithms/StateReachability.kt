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
package edu.kit.iti.formal.automation.testtables.algorithms

import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.Region
import edu.kit.iti.formal.automation.testtables.model.TableRow

/**
 * Calculation of the TableRow/Row initTable.
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
 * This resolution is programmed as a fixpoint algorithm.
 * Currently supports of blocks and arbitrary durations.
 *
 *
 * @author Alexander Weigl
 * @version 2 (12.12.16)
 */
class StateReachability(root: Region) {
    val startSentinel: TableRow = TableRow("START")
    val endSentinel: TableRow = TableRow("END")
    private val flatList: MutableList<TableRow>

    init {
        startSentinel.duration = Duration.ClosedInterval(1, 1)
        endSentinel.duration = Duration.ClosedInterval(1, 1)
        flatList = ArrayList(root.flat())
        flatList.add(endSentinel)
        flatList.add(startSentinel)

        val startSet = hashSetOf(startSentinel)
        val endRows = initTable(startSet, root)
        endRows.forEach {
            if (it.duration !is Duration.Omega) {
                it.outgoing.add(endSentinel)
            }
        }

        // addRegions(root)
        fixpoint()
        maintainIncomning()
        // maintainAutomata()
        isInitialReachable()
    }

/*
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
        state.isEndState = state.outgoing.contains(endSentinel)
    }
}

private fun connect(a: TableRow.AutomatonState, b: TableRow.AutomatonState) {
    a.outgoing.add(b)
    b.incoming.add(a)
}
*/

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
            // for each row
            for (state in flatList) {
                val oldSize = state.outgoing.size
                val reached = HashSet<TableRow>(flatList.size)
                // foreach reachable state
                for (reachable in state.outgoing) {
                    // if reachable state is isSkippable, add their reachable state list
                    if (reachable.duration.isSkippable) {
                        reached.addAll(reachable.outgoing)
                    }
                }
                // add to the outgoing
                state.outgoing.addAll(reached)
                // check for size
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

        // Regions can be isSkippable
        r.children.forEach {
            if (it is Region) addRegions(it)
        }
    }

    /**
     * Initialize the table with the direct initTable.
     * 1. i-th row can reach (i+1)-th row,
     *    except it is within an group with omega duration.
     * 2. End of the region, to beginning of a region.
     except it is within an group with omega duration.
     * 3. Abort on \omega!
     */
    private fun initTable(lastRows: Set<TableRow>, region: Region): MutableSet<TableRow> {
        var lastRows = lastRows.toMutableSet()
        if (region.duration.isRepeatable) {
            val last = region.flat().last()
            if (last.duration !is Duration.Omega) {
                lastRows.add(last)
            }
        }

        for (tn in region.children) {
            when (tn) {
                is TableRow -> {
                    lastRows.forEach { it.outgoing.add(tn) }
                    lastRows.clear()
                    lastRows.add(tn)
                }
                is Region -> {
                    val lr = initTable(lastRows, tn)
                    if (!tn.duration.isSkippable) {
                        lastRows.clear()
                    }
                    lastRows.addAll(lr)
                }
            }
            if (tn.duration is Duration.Omega) {
                lastRows.clear()
            }
        }
        if (region.duration is Duration.Omega) lastRows.clear()
        return lastRows
    }

    private fun isInitialReachable() {
        startSentinel.outgoing.forEach { it.isInitialReachable = true }

        /*val queue = LinkedList<TableRow>()
        queue.add(flatList[0])
        while (!queue.isEmpty()) {
            val s = queue.remove()
            //already reached
            if (s.isInitialReachable)
                continue

            s.isInitialReachable = true

            if (s.duration.isSkippable)
                queue.addAll(s.outgoing)
        }*/
    }
}
