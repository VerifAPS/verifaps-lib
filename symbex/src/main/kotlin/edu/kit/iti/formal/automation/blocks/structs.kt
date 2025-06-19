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

import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.collections.ArrayList
import kotlin.collections.HashSet

data class BlockProgram(
    val blocks: MutableList<Block> = arrayListOf(),
    val edges: MutableList<Pair<Block, Block>> = arrayListOf(),
    val scope: Scope = Scope(),
) {

    val symbex = SymbolicExecutioner(scope)

    fun addAll(subbp: BlockProgram) {
        blocks.addAll(subbp.blocks)
        edges.addAll(subbp.edges)
    }

    fun outgoingEdges(it: Block) = edges.asSequence().filter { (a, _) -> a == it }
    fun incomingEdges(it: Block) = edges.asSequence().filter { (_, b) -> b == it }

    fun findBlockByLabel(lbl: String) = blocks.find { it.label == lbl }

    fun topsorted(): List<Block> {
        val e = ArrayList(edges)
        val sorted = ArrayList<Block>(blocks.size)
        val unsorted = ArrayList(blocks)
        for (i in 0..blocks.size) {
            if (unsorted.isEmpty()) break
            val blocksWOIncoming = unsorted.filter {
                !e.any { (_, to) -> to == it }
            }

            unsorted.removeAll(blocksWOIncoming)
            sorted.addAll(blocksWOIncoming)

            val outgoingEdges = e.filter { (from, _) ->
                from in blocksWOIncoming
            }
            e.removeAll(outgoingEdges)
        }

        if (blocks.size != sorted.size) {
            throw IllegalStateException("Something went wrong")
        }
        return sorted
    }

    fun removeBlock(it: Block) {
        blocks.remove(it)
        val o = outgoingEdges(it)
        val i = incomingEdges(it)
        edges.removeAll(o)
        edges.removeAll(i)
    }

    fun hasLoop(start: Block = startBlock): Boolean = findCycle(start) != null

    fun findCycle(start: Block = startBlock): List<Block>? {
        val marked = HashSet<Block>()
        val onStack = Stack<Block>()

        fun explore(v: Block): Boolean {
            marked += v
            onStack += v
            for ((_, to) in outgoingEdges(v)) {
                if (to !in marked) {
                    if (explore(to)) return true
                } else if (to in onStack) {
                    onStack += to
                    return true
                }
            }
            onStack.pop()
            return false
        }

        if (explore(start)) {
            val loop = ArrayList(onStack)
            val s = loop.indexOf(loop.last())
            return loop.subList(s, loop.size - 1)
        }
        return null
    }

    var startBlock
        get() = blocks.first()
        set(value) {
            blocks.remove(value)
            blocks.add(0, value)
        }

    var endBlock
        get() = blocks.last()
        set(value) {
            blocks.remove(value)
            blocks.add(value)
        }
}

data class Block(
    var label: String = getRandomLabel(),
    var executionCondition: Expression = BooleanLit.LTRUE,
    var statements: StatementList = StatementList(),
) {

    lateinit var ssaExecutionCondition: SMVExpr
    var ssaMutation: Map<SVariable, SMVExpr> = hashMapOf()
    var localMutationMap: SymbolicState = SymbolicState()

    val gotoLabel: String?
        get() = if (statements.isNotEmpty()) (statements.last() as? JumpStatement)?.target else null

    val containsGoto: Boolean
        get() {
            val fgv = FindGotoVisitor()
            statements.accept(fgv)
            return fgv.found
        }

    fun removeTerminalGoto() {
        (statements.last() as? JumpStatement)?.also {
            statements.remove(it)
        }
    }

    fun clone(): Block {
        val b = Block(label, executionCondition.clone(), statements.clone())
        // b.ssaExecutionCondition = ssaExecutionCondition.clone()
        // b.ssaMutation = HashMap(ssaMutation)
        b.localMutationMap = SymbolicState(localMutationMap)
        return b
    }
}

val counter = AtomicInteger(10000)
fun getRandomLabel(): String = String.format("b%05d", counter.getAndIncrement()) // Math.random() * 100000).toInt())

class FindGotoVisitor : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}
    var found: Boolean = false

    override fun visit(jump: JumpStatement) {
        found = true
    }
}