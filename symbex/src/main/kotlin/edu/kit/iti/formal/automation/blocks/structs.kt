package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.st.ast.BooleanLit
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.JumpStatement
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.concurrent.atomic.AtomicInteger

data class BlockProgram(
        val blocks: MutableList<Block> = arrayListOf(),
        val edges: MutableList<Pair<Block, Block>> = arrayListOf()) {
    fun addAll(subbp: BlockProgram) {
        blocks.addAll(subbp.blocks)
        edges.addAll(subbp.edges)
    }

    fun outgoingEdges(it: Block) = edges.asSequence().filter { (a, _) -> a == it }
    fun incomingEdges(it: Block) = edges.asSequence().filter { (_, b) -> b == it }

    fun findBlockByLabel(lbl: String) = blocks.find { it.label == lbl }


    fun removeBlock(it: Block) {
        blocks.remove(it)
        val o = outgoingEdges(it)
        val i = incomingEdges(it)
        edges.removeAll(o)
        edges.removeAll(i)
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
                 val statements: StatementList = StatementList()) {

    var mutationMap: Map<SVariable, SMVExpr> = hashMapOf()

    var cumulatedExecutionCondition = executionCondition

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
