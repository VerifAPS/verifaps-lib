package edu.kit.iti.formal.automation.oo

import edu.kit.iti.formal.automation.st.ast.PouElements

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.12.18)
 */
interface CTransformation {
    fun translate(state: CTState): CTState
    operator fun plus(x: CTransformation): CTransformationPipeline =
            CTransformationPipeline(arrayListOf(this, x))
}

class CTransformationPipeline(
        val seq: MutableList<CTransformation>) : CTransformation {
    override fun translate(state: CTState): CTState {
        return seq.fold(state) { s, t -> t.translate(s) }
    }
}


data class CTState(val pouElements: PouElements)

/**
 *
 */
object ClassMethodCompletion : CTransformation {
    override fun translate(state: CTState): CTState {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}
