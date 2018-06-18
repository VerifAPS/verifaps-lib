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

import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st.util.AstTraversal
import edu.kit.iti.formal.automation.st0.STSimplifier
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.automation.visitors.Visitor
import java.util.*

/**
 * @author Augusto Modanese
 */
class StructEmbedding : ST0Transformation {
    private var state: STSimplifier.State? = null

    override fun transform(state: STSimplifier.State) {
        this.state = state
        process(state.functions.values)
        process(state.theProgram!!)
    }

    private fun process(visitables: Collection<Visitable>) {
        visitables.forEach { this.process(it) }
    }

    private fun process(visitable: Visitable) {
        val structEmbeddingVisitor = StructEmbeddingVisitor()
        visitable.accept(structEmbeddingVisitor)
        for (renameVisitor in structEmbeddingVisitor.renameVisitors) {
            state!!.functions.values.forEach { f -> f.accept(renameVisitor) }
            state!!.theProgram!!.accept(renameVisitor)
        }
    }

    private class StructEmbeddingVisitor : AstTraversal() {

        internal val renameVisitors: MutableList<Visitor<Any>> = ArrayList()

        override fun visit(localScope: Scope) {
            localScope
                    .filter { it.dataType.obj is RecordType }
                    .forEach {
                        val struct = it.dataType as RecordType
                        struct.fields.forEach { field ->
                            localScope.add(createStructVariable(field, it))
                        }
                        renameVisitors.add(StructRenameVisitor(it.name, struct))
                        localScope.asMap().remove(it.name)
                    }
        }

        private fun createStructVariable(field: VariableDeclaration,
                                         structVariable: VariableDeclaration): VariableDeclaration {
            val initialization = structVariable.typeDeclaration!!.initialization as StructureInitialization?
            val newVariable = VariableDeclaration(structVariable.name + "$" + field.name,
                    structVariable.type or field.type,
                    field.dataType.obj!!)
            newVariable.typeDeclaration!!.baseType = field.dataType.copy()
            if (initialization != null)
                newVariable.typeDeclaration!!.setInit(initialization.initValues[field.name])
            return newVariable
        }
    }

    private class StructRenameVisitor(private val structName: String,
                                      private val structType: RecordType) : AstMutableVisitor() {

        override fun visit(invocation: Invocation): Expression {
            for (parameter in ArrayList<InvocationParameter>(invocation.parameters)) {
                if (parameter.expression is SymbolicReference) {
                    val symbolicReference = parameter.expression as SymbolicReference
                    if (symbolicReference.identifier == structName && !symbolicReference.hasSub()) {
                        // Found structure being passed as parameter
                        invocation.parameters.remove(parameter)
                        for (field in structType.fields)
                            invocation.addParameter(InvocationParameter(
                                    if (parameter.name != null)
                                        "${parameter.name}$${field.name}"
                                    else
                                        null,
                                    parameter.isOutput,
                                    SymbolicReference("$structName$${field.name}")))
                    }
                }
            }
            return super.visit(invocation)
        }

        override fun visit(symbolicReference: SymbolicReference): Expression {
            return if (symbolicReference.identifier == structName && symbolicReference.hasSub())
                SymbolicReference(structName + "$" + symbolicReference.sub!!.identifier)
            else super.visit(symbolicReference)
        }
    }
}

