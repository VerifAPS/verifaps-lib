package edu.kit.iti.formal.automation.blocks

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import java.util.*
import kotlin.collections.HashSet

/**
First step, given a list of statements, we break up into multiple blocks by label statements.
 */
fun splitUpByLabel(list: StatementList): BlockProgram {
    val blockProgram = BlockProgram()

    val id = getRandomLabel()
    list.add(LabelStatement("__END__$id"))
    var currentBlock = Block("__START__$id")
    blockProgram.blocks.add(currentBlock)

    list.forEach {
        when (it) {
            is LabelStatement -> {
                val newBlock = Block(it.label)
                blockProgram.blocks.add(newBlock)
                blockProgram.edges.add(currentBlock to newBlock)
                currentBlock = newBlock
            }
            else -> {
                currentBlock.statements.add(it)
            }
        }
    }

    return blockProgram
}

/**
 * Write a block diagram into a dot-file
 */
fun writeDotFile(blocks: BlockProgram): String = StringBuilder().run {
    append("digraph G {\n")

    blocks.blocks.forEach {
        val map = if (it.ssa.isNotEmpty()) it.ssa else it.localMutationMap
        val ssa = map.toList().joinToString("\\n") { (v, e) ->
            "$v = $e"
        }
        val label = listOf(
                it.label,
                IEC61131Facade.print(it.executionCondition),
                IEC61131Facade.print(it.statements).replace("\n", "\\n"),
                ssa).joinToString(" | ")

        append("${it.label} [label=\"{$label}\",shape=\"record\"];\n")
    }

    blocks.edges.forEach { (a, b) ->
        append("${a.label} -> ${b.label} [];\n")
    }

    append("}")

    toString()
}

fun splitGotoBlocks(blocks: BlockProgram) {
    val gotoBlocks = blocks.blocks.filter { it.containsGoto }
    gotoBlocks.forEach {
        val split = splitGoto(it)
        patch(blocks, it, split)
    }

    redrawGotoEdges(blocks)
    truncateUnreachableBlocks(blocks)
    removeEmptyBlocks(blocks)
}

fun truncateUnreachableBlocks(blocks: BlockProgram, start: Block = blocks.startBlock) {
    val allBlocks = blocks.blocks.toMutableSet()
    val reached = HashSet<Block>()
    val queue = LinkedList<Block>()
    queue.add(start)
    while (queue.isNotEmpty()) {
        val b = queue.pop()
        if (b in reached) continue
        reached.add(b)
        blocks.outgoingEdges(b).forEach { (_, to) ->
            queue.add(to)
        }
    }

    val removal = allBlocks - reached
    removal.forEach {
        blocks.removeBlock(it)
    }
}

fun patch(into: BlockProgram, substituted: Block, substitute: BlockProgram) {
    val outgoing = into.outgoingEdges(substituted).toList()
    //val incoming = into.incomingEdges(substituted)

    substituted.statements.clear()


    into.addAll(substitute)
    //into.blocks.remove(substituted)
    into.edges.removeAll(outgoing)
    //into.edges.removeAll(incoming)

    val sb = substitute.startBlock
    val eb = substitute.endBlock

    /*incoming.forEach { (a, _) ->
        into.edges += (a to sb)
    }*/

    into.edges += (substituted to sb)

    outgoing.forEach { (_, b) ->
        into.edges += (eb to b)
    }
}


fun splitGoto(it: Block): BlockProgram {
    val bp = it.statements.accept(GotoSplitter())
    return bp
}

/** Searches for blocks, that do not contain any statments and merges the path condition with the outgoing */
fun removeEmptyBlocks(bp: BlockProgram) {
    val empty = bp.blocks.filter {
        it.statements.isEmpty()
                && it != bp.startBlock && it != bp.endBlock
                && it.executionCondition == BooleanLit.LTRUE
    }

    for (b in empty) {
        val outE = bp.outgoingEdges(b).toList()
        val inE = bp.incomingEdges(b).toList()

        if (outE.size > 1 || inE.size > 1) continue

        inE.forEach { (from, _) -> outE.forEach { (_, to) -> bp.edges += from to to } }
        bp.removeBlock(b)
    }
}

fun redrawGotoEdges(bp: BlockProgram) {
    val gotoBlock = bp.blocks.filter { it.gotoLabel != null }
    gotoBlock.forEach {
        val outgoing = bp.outgoingEdges(it)
        bp.edges.removeAll(outgoing)

        val lbl = it.gotoLabel
        val target = bp.findBlockByLabel(lbl!!)

        if (target != null) {
            bp.edges += (it to target)
            it.removeTerminalGoto()
        } else {
            println("Could not find label: $lbl")
        }
    }
}


/**
 *
 */
class GotoSplitter : AstVisitor<BlockProgram>() {
    override fun defaultVisit(obj: Any): BlockProgram {
        throw IllegalStateException("$obj not supported by ${this.javaClass}")
    }

    override fun visit(statements: StatementList): BlockProgram {
        val bp = BlockProgram()
        var b = Block()
        var end = Block()
        bp.blocks.add(b)

        loop@ for (it in statements) {
            when (it) {
                is AssignmentStatement -> b.statements.add(it)
                is ReturnStatement -> b.statements.add(it)
                is ExitStatement -> b.statements.add(it)
                is JumpStatement -> {
                    b.statements.add(it)
                    break@loop
                }
                else -> {
                    val subbp = it.accept(this)
                    bp.addAll(subbp)

                    //from last block to new start block
                    bp.edges += (b to subbp.startBlock)

                    //new output block, is connected with sub program output.
                    b = Block()
                    bp.blocks.add(b)
                    bp.edges += (subbp.endBlock to b)
                }
            }
        }
        bp.blocks += end
        bp.edges += (b to end)
        return bp
    }

    override fun visit(ifStatement: IfStatement): BlockProgram {
        val bp = BlockProgram()
        val id = getRandomLabel()
        val startBlock = Block("START_IF_$id")
        val endBlock = Block("END_IF_$id")
        bp.blocks += startBlock

        var condition: Expression = BooleanLit.LFALSE

        ifStatement.conditionalBranches.forEach {
            condition = condition.not() and it.condition
            val subbp = it.statements.accept(this)
            bp.addAll(subbp)
            bp.edges += (bp.startBlock to subbp.startBlock)
            bp.edges += (subbp.endBlock to endBlock)
            subbp.startBlock.executionCondition = condition
        }

        if (ifStatement.elseBranch.isNotEmpty()) {
            condition = condition.not()
            val subbp = ifStatement.elseBranch.accept(this)
            bp.addAll(subbp)
            bp.edges += (bp.startBlock to subbp.startBlock)
            bp.edges += (subbp.endBlock to endBlock)
            subbp.startBlock.executionCondition = condition
        }

        bp.endBlock = endBlock
        return bp
    }

}