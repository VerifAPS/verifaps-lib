package edu.kit.iti.formal.automation.st0

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.fbd.FbdBody
import edu.kit.iti.formal.automation.il.IlBody
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.SFCImplementation
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st0.trans.*
import edu.kit.iti.formal.util.CodeWriter

open class MultiCodeTransformation(val transformations: MutableList<CodeTransformation> = arrayListOf())
    : CodeTransformation {
    constructor(vararg t: CodeTransformation) : this(t.toMutableList())

    override fun transform(state: TransformationState): TransformationState =
            transformations.fold(state) { s, t -> t.transform(s) }
}

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 2
 */
class SimplifierPipelineST0 : CodeTransformation {
    val pipeline = MultiCodeTransformation()

    fun add(ct: CodeTransformation) = also { pipeline.transformations += ct }

    fun addGlobalVariableListEmbedding() = add(GlobalVariableListEmbedding())
    fun addCallEmbedding() = add(CallEmbedding())
    fun addLoopUnwinding() = add(LoopUnwinding())
    fun addTimerToCounter() = add(TimerSimplifier())
    fun addArrayEmbedding() = add(ArrayEmbedder())
    fun addStructEmbedding() = add(StructEmbedding)
    fun addSFCResetHandling() = add(SFCResetReplacer())

    //fun addRemoveAction() = add(RemoveActionsFromProgram())
    //fun funConstantEmbedding() = add(ConstantEmbedding())  // EXPERIMENTAL
    fun addTrivialBranchReducer() = add(TrivialBranchReducer())

    fun addSfc2St() = add(Sfc2St)
    fun addFbd2St() = add(Fbd2St)
    fun addIl2St() = add(Il2St)

    fun transform(exec: PouExecutable): PouExecutable {
        val state = TransformationState(exec)
        val nState = transform(state)
        exec.scope = nState.scope
        exec.stBody = nState.stBody
        //exec.sfcBody = nState.sfcBody
        return exec
    }

    override fun transform(state: TransformationState): TransformationState =
            pipeline.transform(state)
}

private object Sfc2St : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.sfcBody?.let {
            if (state.stBody.isEmpty())
                IEC61131Facade.translateSfcToSt(state.scope, it, "")
        }
        return state
    }
}

private object Il2St : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.ilBody?.let {
            if (state.stBody.isEmpty())
                state.stBody = IEC61131Facade.translateIl(it)
        }
        return state
    }
}

private object Fbd2St : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.fbdBody?.let {
            if (state.stBody.isEmpty())
                state.stBody = it.asSt()
        }
        return state
    }

    private fun FbdBody.asSt(): StatementList {
        val out = CodeWriter()
        asStructuredText(out)
        return IEC61131Facade.statements(out.stream.toString())
        /*
        fbDiagram.label?.let { lbl -> body.add(LabelStatement(lbl)) }
        fbDiagram.topsorted().forEach {
            when (it) {
                is FbdNode.Jump -> {
                    fbDiagram.findOutputForInput(it.inputSlots.first())?.let { (n, slot) ->
                        val cond = n.getOutputValue(fbDiagram, slot)
                        body.add(Statements.ifthen(cond, JumpStatement(it.target)))
                    }
                }
                is FbdNode.Execute -> {
                    fbDiagram.findOutputForInput(it.inputSlots.first())?.also { (n, slot) ->
                        val cond = n.getOutputValue(fbDiagram, slot)
                        "IF $cond THEN", "END_IF") { body }
                    }
                }
            }
        }*/
    }
}


val PROGRAM_VARIABLE = VariableDeclaration.FLAG_COUNTER.get()

data class TransformationState(
        var scope: Scope,
        var stBody: StatementList = StatementList(),
        var sfcBody: SFCImplementation? = null,
        var fbdBody: FbdBody? = null,
        var ilBody: IlBody? = null) {
    constructor(exec: PouExecutable) : this(exec.scope,
            exec.stBody ?: StatementList(),
            exec.sfcBody, exec.fbBody, exec.ilBody)
}
