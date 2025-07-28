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