package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.smv.ast.SCaseExpression
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable

fun fillBlocksWithMutation(pb: BlockProgram, scope: Scope) {
    pb.blocks.forEach {
        val sstate = SymbExFacade.evaluateStatements(it.statements, scope)
        it.localMutationMap = sstate.toMap()
    }
}

fun ssaForm(pb: BlockProgram, scope: Scope) {
    val blocks = pb.topsorted()
    blocks.forEach {
        val incoming = pb.incomingEdges(it)
                .map { (from, to) -> from }.toList()
        //1. Update execution condition.
        //2. Update state

        if (incoming.isEmpty()) {
            it.executionConditionSSA = SymbExFacade.evaluateExpression(it.executionCondition, scope)
            it.ssa = HashMap(it.localMutationMap)
        } else {
            val combined: MutableMap<SVariable, SMVExpr> =
                    if (incoming.size == 1) {
                        incoming.first().ssa.toMutableMap()
                    } else {
                        val c = HashMap<SVariable, SCaseExpression>()
                        incoming.forEach { b ->
                            val exc = b.executionConditionSSA
                            val incomingSSA = b.ssa
                            incomingSSA.forEach { t, u ->
                                val case = c.computeIfAbsent(t) { SCaseExpression() } as SCaseExpression
                                case.add(exc, u)
                            }
                        }
                        c.map { (t,u) -> t to u.compress() }.toMap().toMutableMap()
                    }
            it.executionConditionSSA = SymbExFacade.evaluateExpression(combined, it.executionCondition, scope)
            val ssa = HashMap(it.localMutationMap)
            it.localMutationMap.forEach { (t, u) ->
                ssa[t] = SymbExFacade.evaluateExpression(combined, u)
            }
            it.ssa = ssa
        }
    }
}