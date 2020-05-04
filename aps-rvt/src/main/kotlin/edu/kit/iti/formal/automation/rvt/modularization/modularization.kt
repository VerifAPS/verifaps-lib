package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.automation.st.util.UsageFinder
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.SMVPrinter
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.conjunction
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.info
import kotlinx.coroutines.runBlocking
import java.io.File
import java.util.*
import kotlin.collections.HashMap
import kotlin.collections.component1
import kotlin.collections.component2
import kotlin.collections.component3
import kotlin.collections.set

/**
 * Defines a context in which two frames should be verified.
 * A ReveContext defines the relation between output and input variables, and also a condition under which
 * the both should be adhered:
 * `cond /\  i \rel i' ==> o \rel o'`
 */
interface ReveContext {
    val condition: SMVExpr
    val inRelation: MutableList<RelatedVariables>
    val outRelation: MutableList<RelatedVariables>

    //fun relationBetween(oldVar: String, newVar: String): SBinaryOperator
    fun createInRelation(old: BlockStatement, new: BlockStatement, oldModule: String, newModule: String): SMVExpr =
            createRelation(old.input, new.input, oldModule, newModule, inRelation)

    fun createOutRelation(old: BlockStatement, new: BlockStatement, oldModule: String, newModule: String): SMVExpr =
            createRelation(old.output, new.output, oldModule, newModule, outRelation)

    fun createRelation(oldVars: MutableList<SymbolicReference>,
                       newVars: MutableList<SymbolicReference>,
                       oldModule: String,
                       newModule: String,
                       specification: MutableList<RelatedVariables>): SMVExpr {
        //TODO find a nice way to reduce specification effort for perfect equivalence
        val ov = oldVars.map { it.identifier }.toMutableSet()
        val nv = newVars.map { it.identifier }.toMutableSet()
        val seq = mutableListOf<SMVExpr>()
        if (specification.isNotEmpty()) {
            for ((o, op, n) in inRelation) {
                //if (o.name in ov && n.name in nv) {
                seq.add(SBinaryExpression(o.prefix(oldModule), op, n.prefix(newModule)))
                //ov.remove(o.name)
                //nv.remove(n.name)
                //}
            }
        } else {
            val common = ov.intersect(nv)
            for (c in common) {
                val a = SVariable(c)
                seq.add(SBinaryExpression(a.inModule(oldModule), SBinaryOperator.EQUAL, a.inModule(newModule)))
            }
        }
        return seq.conjunction(SLiteral.TRUE)
    }

    fun clone(): ReveContext

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


data class TopReveContext(override var inRelation: MutableList<RelatedVariables> = arrayListOf(),
                          override var outRelation: MutableList<RelatedVariables> = arrayListOf(),
                          override var condition: SMVExpr = SLiteral.TRUE) : ReveContext {

    override fun clone() = copy()

    //override fun relationBetween(oldVar: String, newVar: String): SBinaryOperator =
    //        relation.find { it.oldVar.name == oldVar && it.newVar.name == newVar }?.operator ?: SBinaryOperator.EQUAL

    override val isPerfect: Boolean
        get() = onlyEquivalence && condition == SLiteral.TRUE

    override val onlyEquivalence: Boolean
        get() {
            return inRelation.all { it.operator == SBinaryOperator.EQUAL }
        }
}

/*class ReveSubContext(val topContext: ReveContext,
                     val snapshot: SymbolicState = SymbolicState(),
                     newCtx: SymbolicState) : ReveContext {
    override val condition: SMVExpr by lazy {
        //TODO()
        SLiteral.TRUE
    }
    override val inRelation: MutableList<RelatedVariables> by lazy {
        //TODO
        arrayListOf<RelatedVariables>()
    }

    /*override fun relationBetween(oldVar: String, newVar: String): SBinaryOperator {
        TODO("Not yet implemented")
    }*/

    override val onlyEquivalence: Boolean
        get() = TODO("Not yet implemented")

    override val isPerfect: Boolean
        get() = TODO("Not yet implemented")
}*/

data class RelatedVariables(
        val oldVar: SMVExpr,
        val operator: SBinaryOperator,
        val newVar: SMVExpr) {
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
    fun get(old: Frame, new: Frame) = get(old.block, new.block)
            ?: error("Could not found a context for ${old.name} and ${new.name}")

    fun addAll(manager: ReveContextManager) {
        map.putAll(manager.map)
    }
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
    val ctxManager = ReveContextManager()
    val proveStrategy = DefaultEqualityStrategy(this)

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
            info("\tInput-Relation: ${ctx.createInRelation(bold, bnew, "old", "new").repr()}")
            info("\tOutput-Relation: ${ctx.createOutRelation(bold, bnew, "old", "new").repr()}")
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
            //ctxManager.add(bold, bnew, ReveSubContext(context, oldCtx, newCtx))
        }
    }
}


/** Get the name of the callee */
val Invoked?.name: String?
    get() = when (this) {
        is Invoked.Program -> program.name
        is Invoked.FunctionBlock -> fb.name
        is Invoked.Function -> function.name
        is Invoked.Method -> method.name
        is Invoked.Action -> action.name
        null -> null
    }

typealias CallSiteMapping = List<Pair<BlockStatement, BlockStatement>>

object ModFacade {
    fun createModularProgram(entry: PouExecutable,
                             outputFolder: File,
                             prefix: String = ""): ModularProgram {

        val complete = SymbExFacade.simplify(entry)
        val simplifiedFile = File(outputFolder, "${prefix}_${entry.name}_simplified.st")
        info("Write simplified version of '$prefix' to $simplifiedFile")
        simplifiedFile.bufferedWriter().use { IEC61131Facade.printTo(it, complete) }

        info("Maintain frames in $prefix")
        val callSites = updateBlockStatements(complete)

        val (symbex, frameContext) = evaluateProgram(complete)
        val smvFile = File(outputFolder, "${prefix}_${entry.name}_simplified.smv")
        info("Write complete SMV file of '$prefix' to $smvFile")
        smvFile.bufferedWriter().use { symbex.accept(SMVPrinter(CodeWriter(it))) }

        return ModularProgram(entry, complete, symbex, callSites, frameContext)
    }

    private fun evaluateProgram(complete: PouExecutable): Pair<SMVModule, HashMap<BlockStatement, SymbolicState>> {
        class SymbolicExecutionerFC(topLevel: Scope) : SymbolicExecutioner(topLevel) {
            val catch = HashMap<BlockStatement, SymbolicState>()
            override fun visit(blockStatement: BlockStatement): SMVExpr? {
                catch[blockStatement] = SymbolicState(peek())
                return super.visit(blockStatement)
            }
        }

        val se = SymbolicExecutionerFC(complete.scope.topLevel)
        complete.accept(se)
        val moduleBuilder = ModuleBuilder(complete, se.peek())
        moduleBuilder.run()
        return moduleBuilder.module to se.catch
    }

    fun findCallSitePair(old: String, new: String,
                         oldProgram: ModularProgram, newProgram: ModularProgram)
            : Pair<BlockStatement, BlockStatement> {
        val x = oldProgram.findCallSite(old)
                ?: error("Could not find $old")
        val y = newProgram.findCallSite(new)
                ?: error("Could not find $new")
        return x to y
    }

    fun createReveContextsBySpecification(seq: List<String>, oldProgram: ModularProgram, newProgram: ModularProgram): ReveContextManager {
        val cm = ReveContextManager()
        seq.map { createReveContextsBySpecification(it, oldProgram, newProgram, cm) }
        return cm
    }

    fun createReveContextsBySpecification(it: String, oldProgram: ModularProgram, newProgram: ModularProgram,
                                          ctxManager: ReveContextManager) {
        // it == "A.f=A.f#cond#input#output"
        val sharp = it.count { it == '#' }
        val (sitemap, cond, inrel, outrel) = when (sharp) {
            3 -> it.split("#")
            2 -> it.split("#")?.let { (a, b, c) -> listOf(a, b, c, "") }
            1 -> it.split("#")?.let { (a, b) -> listOf(a, b, "", "") }
            0 -> listOf(it, "", "")
            else -> error("Contract format violated: $it should be `X=Y#cond#relation`")
        }
        val (left, right) = if ("=" in sitemap) sitemap.split("=") else listOf(sitemap, sitemap)
        val (bA, bB) = findCallSitePair(left, right, oldProgram, newProgram)

        val ctx = TopReveContext()
        ctx.condition = if (cond.isBlank()) SLiteral.TRUE else SMVFacade.expr(cond)
        ctx.inRelation = if (inrel.isBlank()) arrayListOf() else inrel.split(",").map(::parseRelation).toMutableList()
        ctx.outRelation = if (outrel.isBlank()) arrayListOf() else outrel.split(",").map(::parseRelation).toMutableList()
        ctxManager.add(bA, bB, ctx)
    }

    fun parseRelation(it: String): RelatedVariables {
        val b = SMVFacade.expr(it) as SBinaryExpression
        val left = b.left
        val right = b.right
        return RelatedVariables(left, b.operator, right)
    }


    fun createFrame(cNew: BlockStatement, scope: Scope): Frame {
        return Frame(cNew, scope)
    }

    fun inferBlockAssignable(scope: Scope, block: BlockStatement) {
        val a = UsageFinder.investigate(block)
        val known = a.knownVariables
        val written = a.writtenReferences.map { it.identifier }
        val read = a.readReference.map { it.identifier }
        for (it in known) {
            val w = it.identifier in written
            val r = it.identifier in read
            when {
                w && r -> block.state.add(it)
                r -> block.input.add(it)
                w -> block.output.add(it)
            }
        }

    }

    fun updateBlockStatements(p: PouExecutable) = MaintainBlocks(p).run()

    fun slice(block: BlockStatement, program: ModularProgram): PouExecutable {
        val origin = program.complete.scope
        val scope = Scope()

        val inputs = origin.getAll(block.input, VariableDeclaration.INPUT)
        val state = origin.getAll(block.state, VariableDeclaration.LOCAL)
        val outputs = origin.getAll(block.output, VariableDeclaration.OUTPUT)

        // TODOx check assignable
        scope.variables.addAll(inputs + state + outputs)
        val fbd = FunctionBlockDeclaration(
                block.originalInvoked?.name ?: block.name, scope, block.statements)

        return fbd
    }
}

class ModularProgram(val entry: PouExecutable,
                     val complete: PouExecutable,
                     val symbex: SMVModule,
                     val callSites: List<BlockStatement>,
                     val frameContext: HashMap<BlockStatement, SymbolicState>) {

    fun findCallSite(aa: String): BlockStatement? {
        return callSites.find { it.repr() == aa }
    }

    val frame: Frame
        get() {
            val blockStatement = BlockStatement(complete.name, complete.stBody!!)
            ModFacade.inferBlockAssignable(complete.scope, blockStatement)
            return ModFacade.createFrame(blockStatement, complete.scope)
        }
}

data class CallSiteSpec(val contextPath: List<String>, val number: Int = 0) {
    var statement: BlockStatement? = null

    val inferedContext = HashMap<String, SMVExpr>()
    var specifiedContext: SMVExpr? = null

    fun repr(): String = contextPath.joinToString(".") + ".$number"
    fun correspond(other: CallSiteSpec) =
            contextPath.subList(1, contextPath.lastIndex) == other.contextPath.subList(1, other.contextPath.lastIndex)
                    && other.number == number

    fun isPrefix(ids: List<String>) = ids.size <= contextPath.size && ids.zip(contextPath).all { (a, b) -> a == b }
}


class MaintainBlocks(val entry: PouExecutable) {
    val blocks: MutableList<BlockStatement> = arrayListOf()

    fun run(): MutableList<BlockStatement> {
        val visitor = CallSiteFinderSearcher()
        visitor.vars += entry.name
        entry.accept(visitor)
        return blocks
    }

    private inner class CallSiteFinderSearcher : AstVisitorWithScope<Unit>() {
        val vars: Stack<String> = Stack()
        var invocationCounter = HashMap<String, Int>()

        val fqName
            get() = vars.joinToString(".")

        private fun endCall() {
            vars.pop()
        }

        private fun startCall(c: BlockStatement): CallSiteSpec {
            vars.push(c.name)
            val n = fqName
            val currentNo = invocationCounter.computeIfAbsent(n) { 0 }
            val cs = CallSiteSpec(vars.toList(), currentNo)
            c.fqName = n
            c.number = currentNo
            invocationCounter[n] = 1 + currentNo

            if (c.state.isEmpty() && c.input.isEmpty() && c.output.isEmpty()) {
                info("Trigger inference of assignable for callsite ${c.repr()}")
                ModFacade.inferBlockAssignable(entry.scope, c)
            }
            return cs
        }

        override fun defaultVisit(obj: Any) {}

        override fun visit(blockStatement: BlockStatement) {
            val ctx = startCall(blockStatement)
            blocks.add(blockStatement)
            visit(blockStatement.statements)
            endCall()
        }
    }
}

private fun Scope.getAll(vars: MutableList<SymbolicReference>, newType: Int = 0) =
        vars.map { reference -> this.getVariable(reference).clone().also { it.type = newType } }
