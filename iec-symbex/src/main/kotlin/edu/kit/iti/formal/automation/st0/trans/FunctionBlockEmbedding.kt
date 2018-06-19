package edu.kit.iti.formal.automation.st0.trans

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.STSimplifier
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (28.06.17)
 */
class FunctionBlockEmbedding : ST0Transformation {
    override fun transform(state: STSimplifier.State) {
        for (vd in state.theProgram!!.scope) {
            vd.type = vd.type or STSimplifier.PROGRAM_VARIABLE
        }

        val cws = CodeWithScope(state.theProgram!!)
        state.theProgram!!.stBody = embeddFunctionBlocks(cws)
    }

    /**
     * first embedds the variables for each function block
     */
    private fun embeddFunctionBlocks(outer: CodeWithScope): StatementList {
        val decls = HashSet(outer.scope.variables)
        val ae = ActionEmbedder(outer)
        outer.statements = ae.embedd()

        for (vd in decls) {
            val type = vd.dataType
            if (type is FunctionBlockDataType) {
                val inner = CodeWithScope(type.functionBlock)
                outer.statements = embeddFunctionBlocksImpl(outer, vd, inner)
            }
        }
        return outer.statements
    }


    private fun embeddFunctionBlocksImpl(outer: CodeWithScope, instance: VariableDeclaration, inner: CodeWithScope): StatementList {
        assert(!outer.statements.isEmpty())

        //recursive call:
        val toBeEmbedded = embeddFunctionBlocks(inner)

        val prefix = instance.name + "$"
        //rename function
        val newName = { s: String -> prefix + s }

        val embeddVariables = prefixNames(inner.scope, newName)

        //declare new variables
        outer.scope.addVariables(embeddVariables)

        // remove FunctionBlock Instance
        outer.scope.asMap().remove(instance.name)

        //Make a clone of the statements and add prefix to every variable
        val vr = VariableRenamer(toBeEmbedded.clone(), newName)
        val prefixedStatements = vr.rename() // <- this can be injected

        // inject into every function block call
        val fbe = FunctionBlockEmbedder(
                instanceName = instance.name,
                toEmbedd = prefixedStatements,
                renameVariable = newName)


        inner.actions.forEach { n, s ->
            //TODO strange that I do not need a variable renaming here
            //VariableRenamer v = new VariableRenamer(s, newName);
            fbe.actions[n] = s // <- this can be injected
        }

        return fbe.embedd(outer.statements)
    }

    private fun prefixNames(scope: Scope, newName: (String) -> String): Scope {
        val copy = Scope().clone()
        for (vd in scope) {
            val nd = vd.clone()
            if (nd.isInput || nd.isInOut || nd.isOutput) {
                val mask = VariableDeclaration.INPUT or
                        VariableDeclaration.INOUT or
                        VariableDeclaration.OUTPUT
                nd.type = nd.type and mask.inv() or VariableDeclaration.LOCAL
            }
            nd.name = newName(nd.name)
            copy.add(nd)
        }
        return copy
    }

    internal class CodeWithScope(internal var scope: Scope, internal var statements: StatementList) {
        internal var actions: MutableMap<String, StatementList> = HashMap()

        constructor(theProgram: ProgramDeclaration)
                : this(scope = theProgram.scope, statements = theProgram.stBody!!.clone()) {
            theProgram.actions.forEach { k -> actions[k.name] = k.stBody!! }
        }

        constructor(fbd: FunctionBlockDeclaration)
                : this(scope = fbd.scope, statements = fbd.stBody!!.clone()) {
            fbd.actions.forEach { k -> actions[k.name] = k.stBody!! }
        }
    }

    private inner class ActionEmbedder(internal val cws: CodeWithScope? = null) : AstMutableVisitor() {

        fun embedd(): StatementList {
            return cws!!.statements.accept(this) as StatementList
        }

        override fun visit(fbc: InvocationStatement): Statement {
            //TODO this should be done via the scope.
            // One place to rule function resolving!
            if (cws!!.actions.containsKey(fbc.calleeName)) {
                val statements = StatementList(cws.actions[fbc.calleeName]!!)
                statements.add(0, CommentStatement.single("Call of action: %s", fbc.calleeName))
                statements.add(CommentStatement.single("End of action call: %s", fbc.calleeName))
                return statements
            }
            return super.visit(fbc)
        }
    }
}
