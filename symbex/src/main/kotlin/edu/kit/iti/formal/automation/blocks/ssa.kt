package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.scope.Scope

fun fillBlocksWithMutation(pb: BlockProgram, scope: Scope) {
    pb.blocks.forEach {
        val sstate = SymbExFacade.evaluateStatements(it.statements, scope)
        it.mutationMap = sstate.toMap()
    }
}