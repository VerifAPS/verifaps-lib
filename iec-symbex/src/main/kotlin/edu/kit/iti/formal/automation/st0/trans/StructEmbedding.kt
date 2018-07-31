/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.datatypes.values.VStruct
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st.util.setAll
import edu.kit.iti.formal.automation.st0.TransformationState
import java.util.*

/**
 * @author Augusto Modanese
 * @author Alexander Weigl
 * */
object StructEmbedding : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        val structVars = state.scope.variables.filter { it.dataType is RecordType }
        expandStructureVariables(structVars, state.scope.variables)
        structVars.forEach {
            state.stBody = rewriteBody(it, state.stBody)
        }

        return state
    }
}

private fun rewriteBody(vd: VariableDeclaration, body: StatementList): StatementList = body.accept(StructEmbeddingVisitor(vd)) as StatementList

private fun expandStructureVariables(structVars: List<VariableDeclaration>, scope: VariableScope) {
    scope.removeAll(structVars)
    for (sv in structVars) scope.addAll(createStructVariables(sv))
}

fun createStructVariables(sv: VariableDeclaration): Collection<VariableDeclaration> {
    when (sv.dataType) {
        is RecordType -> { // recursion for struct, => list of variables + prefix
            val rt = sv.dataType as RecordType
            val (_, rv) = (sv.initValue ?: DefaultInitValue.getInit(sv.dataType!!)) as VStruct

            return rt.fields.flatMap {
                createStructVariables(it)
            }.map {
                val v = rv.fieldValues[it.name]
                if (v != null && it.initValue == null)
                    it.initValue = v
                it.name = "${sv.name}$${it.name}"
                it.type = sv.type
                it
            }
        }
        else -> {
            val newVariable = sv.clone() // just clone, prefix in caller
            return Collections.singleton(newVariable)
        }
    }
}


private class StructEmbeddingVisitor(val vd: VariableDeclaration) : AstMutableVisitor() {
    /*override fun visit(invocation: Invocation): Expression {
        val newParameter = ArrayList<InvocationParameter>()
        for (parameter in invocation.parameters) {
            val expr = parameter.expression.accept(this) as Expression
            parameter.expression = expr;
            if (expr is SymbolicReference && expr.identifier == vd.name) {
                newParameter.addAll(expandParameters(parameter,
                        vd.dataType as RecordType,
                        expr))
                // Found structure being passed as parameter
                newParameter.remove(parameter)
            } else newParameter.add(parameter)
        }
        invocation.parameters.setAll(newParameter)
        return invocation
    }*/

    private fun expandParameters(parameter: InvocationParameter,
                                 rt: RecordType,
                                 expr: SymbolicReference)
            : Collection<InvocationParameter> {
        var path = expr.toPath()
        path = path.subList(1, path.size)
        var subFields = rt.fields
        for (it in path) {
            val sub = subFields[it]
                    ?: throw IllegalStateException("Try to access a composed variable, but inner field not found.")
            if (sub.dataType is RecordType)
                subFields = (sub.dataType as RecordType).fields
            else {
                // paramter ends in a single value
                return Collections.singleton(
                        InvocationParameter(
                                if (parameter.name != null) "${parameter.name}"
                                else null,
                                parameter.isOutput,
                                SymbolicReference(expr.toPath().joinToString("$"))))
            }
            break
        }

        return subFields.map {
            InvocationParameter(
                    if (parameter.name != null) "${parameter.name}$${it.name}"
                    else null,
                    parameter.isOutput,
                    SymbolicReference("${expr.toPath().joinToString()}$${it.name}"))
        }
    }

    override fun visit(symbolicReference: SymbolicReference): Expression {
        return if (symbolicReference.identifier == vd.name && symbolicReference.hasSub())
            SymbolicReference(symbolicReference.toPath().joinToString("$"))
        else super.visit(symbolicReference)
    }
}

