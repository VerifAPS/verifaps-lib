package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.BooleanLit
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.JumpStatement
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.collections.ArrayList
import kotlin.collections.HashMap
import kotlin.collections.HashSet

data class BlockProgram(
        val blocks: MutableList<Block> = arrayListOf(),
        val edges: MutableList<Pair<Block, Block>> = arrayListOf(),
        val scope: Scope = Scope()) {
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

data class Block(var label: String = getRandomLabel(),
                 var executionCondition: Expression = BooleanLit.LTRUE,
                 var statements: StatementList = StatementList()) {

    lateinit var ssaExecutionCondition: SMVExpr
    var ssaMutation: Map<SVariable, SMVExpr> = hashMapOf()
    var localMutationMap: Map<SVariable, SMVExpr> = hashMapOf()

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
        //b.ssaExecutionCondition = ssaExecutionCondition.clone()
        //b.ssaMutation = HashMap(ssaMutation)
        b.localMutationMap = HashMap(localMutationMap)
        return b
    }
}

val counter = AtomicInteger(10000)
fun getRandomLabel(): String = String.format("b%05d", counter.getAndIncrement()) //Math.random() * 100000).toInt())

class FindGotoVisitor : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}
    var found: Boolean = false

    override fun visit(jump: JumpStatement) {
        found = true
    }
}
