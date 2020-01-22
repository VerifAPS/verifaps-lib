package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import java.util.*

val EMBEDDING_BODY_PIPELINE = MultiCodeTransformation(arrayListOf(
        ActionEmbedder(),
        FBEmbeddParameters(),
        FBAssignments(),
        FBEmbeddCode()
))


val EMBEDDING_PIPELINE = MultiCodeTransformation(arrayListOf(
        ActionEmbedder(),
        FBEmbeddVariables(),
        EMBEDDING_BODY_PIPELINE,
        FBRemoveInstance()
))


const val SCOPE_SEPARATOR = "$"

class CallEmbedding : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState = EMBEDDING_PIPELINE.transform(state)
}

class ActionEmbedder : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(ActionEmbedderImpl()) as StatementList
        return state
    }

    private class ActionEmbedderImpl : AstMutableVisitor() {
        override fun visit(fbc: InvocationStatement): Statement {
            try {
                val ainvoke = fbc.invoked as Invoked.Action
                val stmt = StatementList()
                stmt += CommentStatement.single("Call of action: %s", fbc.callee.identifier)
                stmt.addAll(ainvoke.action.stBody!!)
                stmt += CommentStatement.single("End of action call: %s", fbc.callee.identifier)
                return stmt
            } catch (e: ClassCastException) {

            }
            return super.visit(fbc)
        }
    }
}

class FBEmbeddVariables : CodeTransformation {
    fun transform(scope: Scope): ArrayList<VariableDeclaration> {
        val variables = arrayListOf<VariableDeclaration>()

        val mask = (VariableDeclaration.INPUT or VariableDeclaration.OUTPUT or VariableDeclaration.INOUT).inv()

        for (vd in scope.variables) {
            val type = vd.dataType
            if (type is FunctionBlockDataType) {
                val subScope = transform(type.functionBlock.scope)
                subScope.forEach {
                    it.name = vd.name + SCOPE_SEPARATOR + it.name
                    it.type = it.type and mask or VariableDeclaration.LOCAL
                }
                variables.addAll(subScope)
            }
            variables.add(vd.clone())
        }

        return variables
    }

    override fun transform(state: TransformationState): TransformationState {
        val vars = transform(state.scope)
        state.scope.variables.clear()
        state.scope.variables.addAll(vars)
        return state
    }
}

class FBEmbeddParameters : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(FBEmbeddParamtersImpl(state)) as StatementList
        return state
    }

    class FBEmbeddParamtersImpl(val state: TransformationState) : AstMutableVisitor() {
        override fun visit(invocation: InvocationStatement): Statement {
            val invoked = invocation.invoked
            if (invoked != null && invoked is Invoked.FunctionBlock) {
                val stmt = StatementList()
                invocation.inputParameters.forEach { (name, _, expression) ->
                    if (name != null) {
                        val sr = invocation.callee.copy(sub = SymbolicReference(name))
                        stmt += AssignmentStatement(sr, expression)
                    } else {
                        throw IllegalStateException("Function block call without parameter name!")
                    }
                }

                stmt += (CommentStatement.single("Call of %s", invocation.callee.identifier))
                stmt += invocation

                //rewrite output variables as trailing assignments.
                invocation.outputParameters.forEach { (name, _, expression) ->
                    if (name != null) {
                        invocation.callee.copy(sub = SymbolicReference(name))
                        stmt += AssignmentStatement(expression as SymbolicReference, SymbolicReference(name))
                    } else {
                        throw IllegalStateException("Output parameter in function block call w/o name.")
                    }
                }
                stmt += CommentStatement.single("End of call")

                //clear all parameters
                invocation.parameters.clear()
                return stmt
            }
            return invocation
        }
    }
}

class FBAssignments : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(FBAssignmentsImpl(state.scope)) as StatementList
        return state
    }

    class FBAssignmentsImpl(private val scope: Scope) : AstMutableVisitor() {
        override fun visit(symbolicReference: SymbolicReference): Expression {
            val s = scope.resolveVariable(symbolicReference)
            val dt = s?.dataType
            if (s != null && dt is FunctionBlockDataType && symbolicReference.hasSub()) {
                return SymbolicReference(symbolicReference.toPath().joinToString("$"))
            }
            return super.visit(symbolicReference)
        }
    }
}

class FBEmbeddCode : CodeTransformation, AstMutableVisitor() {
    companion object {
        private val bodyCache = hashMapOf<TransformationState, StatementList>()
    }

    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(this) as StatementList
        return state
    }

    fun getBody(prefix: String, state: TransformationState): StatementList {
        if (state !in bodyCache) {
            val istate = TransformationState(
                    state.scope, state.stBody.clone(), SFCImplementation())
            val s = EMBEDDING_BODY_PIPELINE.transform(istate)
            bodyCache[state] = s.stBody
        }
        val statements = bodyCache[state]!!
        val renamed =  VariableRenamer(state.scope::isGlobalVariable, statements.clone()) { prefix + SCOPE_SEPARATOR + it }.rename()
        return renamed
    }

    override fun visit(invocation: InvocationStatement): Statement {
        val invoked = invocation.invoked
                ?: throw IllegalStateException("Invocation was not resolved. Abort. $invocation")

        if (invoked is Invoked.FunctionBlock) {
            val state = TransformationState(invoked.fb)
            val prefix = invocation.callee.toPath().joinToString(SCOPE_SEPARATOR)
            return getBody(prefix, state)
        }

        if (invoked is Invoked.Action && invocation.callee.hasSub()) {
            val action = invocation.callee.toPath()
            val fb = action.subList(0, action.lastIndex - 1)
            val prefix = fb.joinToString(SCOPE_SEPARATOR)
            val state = TransformationState(invoked.scope, invoked.action.stBody!!, SFCImplementation())
            return getBody(prefix, state)
        }

        if (invoked is Invoked.Function) {
            val s = StatementList()
            //s += CommentStatement.single("Removed function invocation to ${invoked.function.name}")
            s += CommentStatement.single("TODO for feature: Embedd function body after substitution to cover global effects.")
            s.addAll(invoked.function.stBody!!)
            return s
        }


        return invocation
    }
}

class FBRemoveInstance : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        val fbVars = state.scope.filter { it.dataType is FunctionBlockDataType }
        state.scope.variables.removeAll(fbVars)
        return state
    }
}
