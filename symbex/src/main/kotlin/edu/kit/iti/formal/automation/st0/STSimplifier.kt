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
package edu.kit.iti.formal.automation.st0

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st0.trans.Sfc2StPipelineStep
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.SFCImplementation
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st0.trans.*

open class MultiCodeTransformation(val transformations: MutableList<CodeTransformation> = arrayListOf()) : CodeTransformation {
    constructor(vararg t: CodeTransformation) : this(t.toMutableList())

    override fun transform(state: TransformationState): TransformationState = transformations.fold(state) { s, t ->
        t.transform(s)
    }
}

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 2
 */
class SimplifierPipelineST0 : CodeTransformation {
    val pipeline = MultiCodeTransformation()

    fun add(ct: CodeTransformation) = also { pipeline.transformations += ct }
    fun addGlobalVariableListEmbedding() = add(GlobalVariableListEmbedding())

    fun addSFCReduction() = add(Sfc2StPipelineStep())
    fun addCallEmbedding() = add(CallEmbedding())
    fun addLoopUnwinding() = add(LoopUnwinding())
    fun addTimerToCounter() = add(TimerSimplifier())
    fun addArrayEmbedding() = add(ArrayEmbedder())
    fun addStructEmbedding() = add(StructEmbedding)
    fun addSFCResetHandling() = add(SFCResetReplacer())

    // fun addRemoveAction() = add(RemoveActionsFromProgram())
    // fun funConstantEmbedding() = add(ConstantEmbedding())  // EXPERIMENTAL
    fun addTrivialBranchReducer() = add(TrivialBranchReducer())

    fun transform(exec: PouExecutable): PouExecutable {
        val state = TransformationState(exec)
        val nState = transform(state)
        exec.scope = nState.scope
        exec.stBody = nState.stBody
        // exec.sfcBody = nState.sfcBody
        return exec
    }

    override fun transform(state: TransformationState): TransformationState = pipeline.transform(state)
}

val PROGRAM_VARIABLE = VariableDeclaration.FLAG_COUNTER.get()

data class TransformationState(
    var scope: Scope,
    var stBody: StatementList = StatementList(),
    var sfcBody: SFCImplementation = SFCImplementation(),
) {
    constructor(exec: PouExecutable) : this(
        exec.scope,
        exec.stBody ?: StatementList(),
        exec.sfcBody
            ?: SFCImplementation(),
    )
}