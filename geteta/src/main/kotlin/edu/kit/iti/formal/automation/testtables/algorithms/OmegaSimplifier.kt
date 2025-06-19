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
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.Region
import edu.kit.iti.formal.automation.testtables.model.TableRow
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
class OmegaSimplifier(val product: GeneralizedTestTable) : Runnable {
    val ignored = ArrayList<TableRow>()
    private var abort = false

    override fun run() {
        abort = false
        product.region = recur(product.region)
    }

    /**
     * Traverse and copy the tree structure until an \omega appeares as duration, then
     * fwdprogress traversing but do not copy. The rowStates are capture to [.ignored]
     *
     * @param region
     * @return
     */
    private fun recur(region: Region): Region {
        val newRegion = Region(region.id)
        newRegion.duration = region.duration
        for (state in region.children) {
            if (abort) {
                when (state) {
                    is Region -> recur(state)
                    else -> ignored.add(state as TableRow)
                }
            } else {
                when (state) {
                    is Region ->
                        newRegion.children.add(recur(state))
                    is TableRow ->
                        newRegion.children.add(state)
                }
                if (state.duration === Duration.Omega) abort = true
            }
        }
        return newRegion
    }
}
