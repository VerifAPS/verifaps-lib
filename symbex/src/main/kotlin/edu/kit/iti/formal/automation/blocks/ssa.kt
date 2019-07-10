package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.values.FALSE
import edu.kit.iti.formal.automation.st.ast.BooleanLit
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st.ast.assignTo
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

        //unrollLoops()
    } else {
        ssaTopsort()
    }
}

private fun BlockProgram.prepareSSA() {
    this.blocks.forEach {
        val sstate = SymbExFacade.evaluateStatements(it.statements, scope)
        it.localMutationMap = sstate.toMap()
    }
}

private fun BlockProgram.ensureErrorFlag() {
    val ERROR_FLAG = "__ERROR__"
    if (ERROR_FLAG !in scope.variables) {
        val vd = VariableDeclaration(ERROR_FLAG, VariableDeclaration.LOCAL, AnyBit.BOOL)
        vd.initValue = FALSE
        scope.variables.add(vd)
    }
}

fun BlockProgram.unrollLoops() {
    while (true) {
        val loop = findCycle()
        if (loop != null)
            unrollLoop(loop, 1)//TODO make configurable
        else
            break
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
                from == loopEnd && to == loopStart -> { /* skip */ }
                from in loop && to in loop -> {
                    val newFrom = replacement[from]!!
                    val newTo = replacement[to]!!
                    newProgram.edges += newFrom to newTo
                }
                from in loop -> {
                    val newFrom = replacement[from]!!
                    newProgram.edges += newFrom to to
                }
                //Jump into the loop is not allowed
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
    val errorBlock = Block("unsuff_bounds_$loopId",
            loopStart.executionCondition,
            StatementList("__ERROR__" assignTo BooleanLit.LTRUE))
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

        //1. Update execution condition.
        //2. Update state

        if (incoming.isEmpty()) { //No incoming edge. The terms stands for itself.
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

private fun calcIncomingSymbolicState(incoming: List<Block>): Map<SVariable, SMVExpr> {
    return if (incoming.size == 1) {
        incoming.first().ssaMutation.toMutableMap()
    } else {
        val c = HashMap<SVariable, SCaseExpression>()
        incoming.forEach { b ->
            val exc = b.ssaExecutionCondition
            val incomingSSA = b.ssaMutation
            incomingSSA.forEach { t, u ->
                val case = c.computeIfAbsent(t) { SCaseExpression() } as SCaseExpression
                case.add(exc, u)
            }
        }
        c.map { (t, u) -> t to u.compress() }.toMap().toMutableMap()
    }
}