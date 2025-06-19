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
package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.values.FALSE
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.smv.ast.SCaseExpression
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable

/**
 * Extension for BlockProgram to calculate the SSA form
 */
fun BlockProgram.ssa() {
    ensureErrorFlag()
    prepareSSA()
    if (hasLoop()) {
        throw IllegalStateException("You should remove all loops before you call ssa(). see unrollLoops()")
    } else {
        ssaTopsort()
    }
}

private fun BlockProgram.prepareSSA() {
    this.blocks.forEach {
        symbex.push()
        val program = ProgramDeclaration(scope = scope, stBody = it.statements)
        IEC61131Facade.resolveDataTypes(PouElements.singleton(program))
        program.accept(symbex)
        val sstate = symbex.pop()
        it.localMutationMap = sstate
    }
}

private const val ERROR_FLAG = "__ERROR__"
private fun BlockProgram.ensureErrorFlag() {
    if (ERROR_FLAG !in scope.variables) {
        val vd = VariableDeclaration(ERROR_FLAG, VariableDeclaration.LOCAL, AnyBit.BOOL)
        vd.initValue = FALSE
        scope.variables.add(vd)
    }
}

fun BlockProgram.unrollLoops(k: Int = 1) {
    while (true) {
        val loop = findCycle()
        if (loop != null) {
            unrollLoop(loop, k)
        } else {
            break
        }
    }
}

fun BlockProgram.unrollLoop(loop: List<Block>, k: Int) {
    println(loop)
    val loopStart = loop.first()
    val loopEnd = loop.last()
    val newProgram = BlockProgram()
    val startBlock = Block()
    val endBlock = Block()
    val loopId = getRandomLabel()

    startBlock.label = loopStart.label

    var lastBlock = startBlock

    for (i in 1..k) {
        val copy = loop.clone()
        newProgram.blocks += copy
        copy.forEach { b -> b.label += "#$i" }

        val replacement = loop.zip(copy).toMap()
        edges.forEach { (from, to) ->
            when {
                from == loopEnd && to == loopStart -> {
                    /* skip */
                }
                from in loop && to in loop -> {
                    val newFrom = replacement[from]!!
                    val newTo = replacement[to]!!
                    newProgram.edges += newFrom to newTo
                }
                from in loop -> {
                    val newFrom = replacement[from]!!
                    newProgram.edges += newFrom to to
                }
                // Jump into the loop is not allowed
                // or should it go to the first iteration?
            }
        }

        newProgram.edges += lastBlock to copy.first()

        val exitLoop = Block("__exit#${i}__$loopId", loopStart.executionCondition.not())
        newProgram.blocks += exitLoop
        newProgram.edges += lastBlock to exitLoop
        newProgram.edges += exitLoop to endBlock

        lastBlock = copy.last()
    }
    val errorBlock = Block(
        "unsuff_bounds_$loopId",
        loopStart.executionCondition,
        StatementList("__ERROR__" assignTo BooleanLit.LTRUE),
    )
    newProgram.blocks += errorBlock
    newProgram.edges += lastBlock to errorBlock
    newProgram.edges += errorBlock to endBlock

    newProgram.startBlock = startBlock
    newProgram.endBlock = endBlock

    addAll(newProgram)
    incomingEdges(loopStart).toList().forEach { (from, _) ->
        edges += from to newProgram.startBlock
    }
    outgoingEdges(loopEnd).toList().forEach { (_, to) ->
        edges += newProgram.endBlock to to
    }
    loop.forEach(::removeBlock)
}

private fun Iterable<Block>.clone() = this.map { it.clone() }

private fun BlockProgram.ssaTopsort() {
    val blocks = topsorted()
    blocks.forEach {
        val incoming = incomingEdges(it)
            .map { (from, _) -> from }
            .toList()

        // 1. Update execution condition.
        // 2. Update state
        if (incoming.isEmpty()) { // No incoming edge. The terms stand for itself.
            it.ssaExecutionCondition = SymbExFacade.evaluateExpression(it.executionCondition, scope)
            it.ssaMutation = HashMap(it.localMutationMap)
        } else {
            val combined = calcIncomingSymbolicState(incoming)
            val ssa = HashMap(it.localMutationMap)
            it.ssaExecutionCondition = SymbExFacade.evaluateExpression(combined, it.executionCondition, scope)
            it.localMutationMap.forEach { (t, u) ->
                ssa[t] = SymbExFacade.evaluateExpression(combined, u)
            }
            it.ssaMutation = ssa
        }
    }
}

private fun calcIncomingSymbolicState(incoming: List<Block>): Map<SVariable, SMVExpr> = if (incoming.size == 1) {
    incoming.first().ssaMutation.toMutableMap()
} else {
    val c = HashMap<SVariable, SCaseExpression>()
    incoming.forEach { b ->
        val exc = b.ssaExecutionCondition
        val incomingSSA = b.ssaMutation
        incomingSSA.forEach { t, u ->
            val case = c.computeIfAbsent(t) { SCaseExpression() }
            case.add(exc, u)
        }
    }
    c.map { (t, u) -> t to u.compress() }.toMap().toMutableMap()
}