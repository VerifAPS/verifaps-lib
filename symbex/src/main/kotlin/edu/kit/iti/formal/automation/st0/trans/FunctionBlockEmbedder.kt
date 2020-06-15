package edu.kit.iti.formal.automation.st0.trans

/*-
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

import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import java.util.*

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 1
 */
class FunctionBlockEmbedder(private val instanceName: String,
                            private val toEmbedd: StatementList,
                            private val renameVariable: (String) -> String) : AstMutableVisitor() {
    val actions: MutableMap<String, StatementList> = HashMap()

    override fun visit(symbolicReference: SymbolicReference): Expression {
        if (instanceName == symbolicReference.identifier) {
            if (symbolicReference.sub != null) {
                val field = symbolicReference.sub!!.identifier
                return SymbolicReference("$instanceName$$field")
            }
        }
        return super.visit(symbolicReference)
    }

    override fun visit(statements: StatementList): StatementList {
        val r = StatementList()
        for (s in statements) {
            val visit = s.accept(this) ?: throw IllegalArgumentException("got null for " + s.nodeName)
            if (visit is StatementList) {
                r.addAll(visit)
            } else {
                r.add(visit as Statement)
            }
        }
        return r
    }

    override fun visit(fbc: InvocationStatement): Statement {
        val (identifier, _, sub) = fbc.callee
        if (instanceName != identifier) {
            return super.visit(fbc) // I am not caring about this instance.
        }

        // rewrite input parameters as assignments
        // f(a:=2) ==> f$a:=2; f()
        val sl = StatementList()
        fbc.inputParameters.forEach { (name, _, expression) ->
            if (name != null) {
                val internalName = renameVariable(name)
                sl.add(AssignmentStatement(
                        SymbolicReference(internalName),
                        expression
                ))
            } else {
                error("Function block call without parameter name!")
            }
        }

        sl.add(CommentStatement.single("Call of %s:%s", instanceName, fbc.callee.identifier))
        if (sub == null) {//insert main statement block
            sl.addAll(this.toEmbedd)
        } else {
            val actionName = sub.identifier
            if (actions.containsKey(actionName)) {
                sl.addAll(actions[actionName]!!)
            } else {
                sl.add(CommentStatement.single("//ERROR: COULD NOT FIND ACTION %s.%s",
                        instanceName, actionName))
            }
        }

        //rewrite output variables as trailing assignments.
        fbc.outputParameters.forEach { (name, _, expression) ->
            if (name != null) {
                val name = renameVariable(name)
                val assign = AssignmentStatement(
                        expression as SymbolicReference,
                        SymbolicReference(name)
                )
                sl.add(assign)
            } else {
                error("Output parameter in function block call w/o name.")
            }
        }
        sl.add(CommentStatement.single("End of call"))
        return sl
    }

    fun embedd(into: StatementList): StatementList {
        return into.accept(this) as StatementList
    }
}
