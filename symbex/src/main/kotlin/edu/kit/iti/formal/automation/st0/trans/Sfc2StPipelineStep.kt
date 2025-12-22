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
package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.sfclang.*
import edu.kit.iti.formal.automation.st0.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (7/16/25)
 */
class Sfc2StPipelineStep : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        if (state.stBody.isEmpty() && state.sfcBody.networks.isNotEmpty()) {
            require(state.sfcBody.networks.size == 1)
            for (network in state.sfcBody.networks) {
                val s2s = SFC2ST("", network, state.scope)
                state.stBody = s2s.get()
            }
        }

        IEC61131Facade.resolveDataTypes(state.scope, state.stBody)
        return state
    }
}