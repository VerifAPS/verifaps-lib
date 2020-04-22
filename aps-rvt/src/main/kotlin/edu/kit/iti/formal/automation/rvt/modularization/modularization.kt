package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.st.ast.BlockStatement
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.info
import kotlinx.coroutines.runBlocking
import java.io.File

/**
 * Defines a context in which two frames should be verified.
 * A ReveContext defines the relation between output and input variables, and also a condition under which
 * the both should be adhered:
 * `cond /\  i \rel i' ==> o \rel o'`
 */
interface ReveContext {
    val condition: SMVExpr
    val relation: MutableList<RelatedVariables>

    fun relationBetween(oldVar: String, newVar: String): SBinaryOperator

    val onlyEquivalence: Boolean
    val isPerfect: Boolean
}

/**
 * Sub context relation, we are using an heuristic.
 */
operator fun ReveContext.compareTo(c: ReveContext): Int {
    if (c.isPerfect) {
        if (isPerfect) return 0
        return -1
    }
    return 1
}


class TopReveContext : ReveContext {
    override var relation: MutableList<RelatedVariables> = arrayListOf()
    override var condition: SMVExpr = SLiteral.TRUE

    override fun relationBetween(oldVar: String, newVar: String): SBinaryOperator =
            relation.find { it.oldVar.name == oldVar && it.newVar.name == newVar }?.operator ?: SBinaryOperator.EQUAL

    fun inputs(old: Frame, new: Frame): MutableList<RelatedVariables> = TODO()
    fun outputs(old: Frame, new: Frame): MutableList<RelatedVariables> = TODO()

    override val isPerfect: Boolean
        get() = onlyEquivalence && condition == SLiteral.TRUE

    override val onlyEquivalence: Boolean
        get() {
            return relation.all { it.operator == SBinaryOperator.EQUAL }
        }
}

class ReveSubContext(val topContext: ReveContext,
                     val snapshot: SymbolicState = SymbolicState(),
                     newCtx: SymbolicState) : ReveContext {
    override val condition: SMVExpr by lazy {
        //TODO()
        SLiteral.TRUE
    }
    override val relation: MutableList<RelatedVariables> by lazy {
        //TODO
        arrayListOf<RelatedVariables>()
    }

    override fun relationBetween(oldVar: String, newVar: String): SBinaryOperator {
        TODO("Not yet implemented")
    }

    override val onlyEquivalence: Boolean
        get() = TODO("Not yet implemented")

    override val isPerfect: Boolean
        get() = TODO("Not yet implemented")
}

data class RelatedVariables(
        val oldVar: SVariable,
        val operator: SBinaryOperator,
        val newVar: SVariable) {
    val expr
        get() = SBinaryExpression(oldVar, operator, newVar)
}

class ReveContextManager {
    val pairs: List<Pair<BlockStatement, BlockStatement>>
        get() = map.keys.toList()

    private val map = HashMap<Pair<BlockStatement, BlockStatement>, ReveContext>()
    fun add(old: BlockStatement, new: BlockStatement, ctx: ReveContext) {
        map[old to new] = ctx
    }

    fun get(old: BlockStatement, new: BlockStatement) = map[old to new]
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.07.18)
 */
class ModularProver(
        val oldProgram: ModularProgram,
        val newProgram: ModularProgram,
        var context: ReveContext,
        var callSitePairs: CallSiteMapping = arrayListOf(),
        var outputFolder: File = File(".")
) {
    val proveStrategy = DefaultEqualityStrategy(this)
    var ctxManager = ReveContextManager()

    fun printCallSites() {
        info("Call sites for the old program: ${oldProgram.entry.name}")
        oldProgram.callSites.forEach {
            info("${it.repr()} in line ${it.startPosition}, embedded from ${it.originalInvoked.name}")
        }
        info("Call sites for the new program: ${newProgram.entry.name}")
        newProgram.callSites.forEach {
            info("${it.repr()} in line ${it.startPosition}, embedded from ${it.originalInvoked.name}")
        }

        callSitePairs.forEach { (bold, bnew) ->
            val ctx = ctxManager.get(bold, bnew) ?: error("no context found")
            info("Matched ${bold.repr()} to ${bnew.repr()}")
            info("\tContext: ${ctx.condition.repr()}")
            info("\tRelation: ${ctx.relation}")
        }
    }

    fun proof() {
        outputFolder.mkdirs()
        runBlocking(ModApp.processContext) {
            val equal = proveStrategy.proofEquivalenceTopLevel()
            info("Proof result: $equal")
        }
    }

    fun inferReveContexts() {
        callSitePairs.forEach { (bold, bnew) ->
            val oldCtx = oldProgram.frameContext[bold]!!
            val newCtx = newProgram.frameContext[bnew]!!
            ctxManager.add(bold, bnew, ReveSubContext(context, oldCtx, newCtx))
        }
    }
}
