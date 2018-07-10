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

import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.Region
import edu.kit.iti.formal.automation.testtables.model.State
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
class OmegaSimplifier(val product: GeneralizedTestTable) : Runnable {
    val ignored = ArrayList<State>()
    private var abort = false

    override fun run() {
        abort = false
        product.region = recur(product.region)
    }

    /**
     * Traverse and copy the tree structure until an \omega appeares as duration, then
     * keep traversing but do not copy. The states are capture to [.ignored]
     *
     * @param region
     * @return
     */
    private fun recur(region: Region?): Region {
        val newRegion = Region(region!!.id)
        for (state in region.children) {
            if (abort) {
                when (state) {
                    is Region -> recur(state)
                    else -> ignored.add(state as State)
                }
            } else {
                when (state) {
                    is Region ->
                        newRegion.children.add(recur(state as Region))
                    is State ->
                        newRegion.children.add(state)
                }
                if (state.duration === Duration.Omega) abort = true
            }
        }
        return newRegion
    }
}
