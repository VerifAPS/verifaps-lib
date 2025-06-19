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
@file:Suppress("MemberVisibilityCanBePrivate")

package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.USINT
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.modularization.ModFacade.createFrame
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.smt.DefaultS2SFunctionTranslator
import edu.kit.iti.formal.automation.smt.DefaultS2STranslator
import edu.kit.iti.formal.automation.smt.Smv2SmtVisitor
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.smt.*
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.info
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withContext
import java.io.File
import java.math.BigInteger
import java.util.*
import kotlin.collections.HashMap
import kotlin.collections.HashSet

val TYPE_COUNTER = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.LOCAL
val TYPE_INPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.OUTPUT
val TYPE_OUTPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.INPUT

data class Frame(val block: BlockStatement, val scope: Scope) {
    val name: String
        get() = block.fqName
}

class DefaultEqualityStrategy(mp: ModularProver) {
    var disableProofBodyEquivalenceSMT = false
    var disableProofBodyEquivalenceSSA = false
    var disableProofBodyEquivalenceSource = false
    var disableProofBodyEquivalenceWithAbstractionSubFrames = false
    var disableProofBodyEquivalenceWithAbstractionBody = false
    var disableProofBodyEquivalenceWithAbstraction = false
    var disableProofBodyEquivalenceClassic = false
    var disableUpdateCache = false
    var disableCheckCache = false

    var assumeAsProven = TreeSet<String>()

    val reveContextManager: ReveContextManager = mp.ctxManager

    val outputFolder = mp.outputFolder
    val callSitePairs = mp.callSitePairs

    val oldProgram = mp.oldProgram
    val newProgram = mp.newProgram
    val topLevelContext = mp.context

    val smvCache = HashMap<Frame, SymbolicState>()

    /*suspend*/
    fun proofEquivalenceTopLevel() = proofEquivalence(oldProgram.frame, newProgram.frame, topLevelContext)

    /*suspend*/
    fun proofEquivalence(old: Frame, new: Frame, ctx: ReveContext = reveContextManager.get(old, new)): Boolean {
        val lp = logprfx("proofEquivalence", old, new)

        info("$lp ${old.block.repr()}: ${printStatistic(old)}")
        info("$lp ${new.block.repr()}: ${printStatistic(new)}")

        var equal = false

        if (lp.trim() in assumeAsProven) {
            info("$lp Proven by assumption")
            equal = true
        }

        val stat = StopWatch()

        if (!equal) stat.time("cache") { equal = checkCache(old, new, ctx) }

        if (!equal) {
            stat.time("src") {
                equal = proofBodyEquivalenceSource(old, new, ctx)
            }
        }
        if (!equal) {
            stat.time("ssa") {
                equal = proofBodyEquivalenceSSA(old, new, ctx)
            }
        }
        if (!equal) {
            stat.time("smt") {
                equal = proofBodyEquivalenceSMT(old, new, ctx)
            }
        }
        if (!equal) {
            stat.time("mod") {
                equal = proofBodyEquivalenceWithAbstraction(old, new, ctx)
            }
        }
        if (!equal) {
            stat.time("cmc") {
                equal = proofBodyEquivalenceClassic(old, new, ctx)
            }
        }
        if (equal) updateCache(old, new, ctx, equal)

        info("$lp Timings: $stat")
        return equal
    }

    //region caching
    private val equivCache = arrayListOf<Triple<String, String, ReveContext>>()
    private fun checkCache(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx("checkCache", old, new)

        if (disableCheckCache) {
            info("$lp Skipped because `disableCheckCache` is set")
            return false
        }

        val oldInstance = old.block.originalInvoked.name
        val newInstance = new.block.originalInvoked.name
        val r = equivCache.any { (a, b, c) -> oldInstance == a && b == newInstance && ctx <= c }
        if (r) {
            info("$lp Cache hit for equiv. proof of $oldInstance with $newInstance")
        } else {
            info("$lp Cache miss equiv. proof of $oldInstance with $newInstance")
        }
        return r
    }

    private fun updateCache(old: Frame, new: Frame, ctx: ReveContext, equal: Boolean) {
        val lp = logprfx("updateCache", old, new)

        if (disableUpdateCache) {
            info("$lp Skipped because `disableUpdateCache` is set")
            return
        }
        // TODO Consider using a hash-value of the source if there is no originalInvoked name.
        val oldInstance = old.block.originalInvoked.name
        val newInstance = new.block.originalInvoked.name
        if (equal && oldInstance != null && newInstance != null) {
            equivCache.add(Triple(oldInstance, newInstance, ctx))
            info("$lp Update cache with $oldInstance and $newInstance")
        }
    }
    //endregion

    /**
     * Proofs the equivalence of the given frames without respect to the
     */
    /*suspend*/
    fun proofBodyEquivalenceClassic(
        old: Frame,
        new: Frame,
        ctx: ReveContext = reveContextManager.get(old, new),
    ): Boolean {
        val lp = logprfx("proofBodyEquivalenceClassic", old, new)

        if (disableProofBodyEquivalenceClassic) {
            info("$lp Skipped because `disableProofBodyEquivalenceClassic` is set")
            return false
        }

        val oldSmv = smv(old, symbex(old, true))
        val newSmv = smv(new, symbex(new, true))

        if (oldSmv.name == newSmv.name) { // name clash!
            oldSmv.name += "old"
            newSmv.name += "new"
        }

        val modules = glueWithMiter(old, new, oldSmv, newSmv, ctx)
        val smvFile = file("${old.name}_${new.name}.smv")
        val logFile = file("${old.name}_${new.name}.log")

        info("$lp Starting proof: $smvFile, $logFile")

        val r = runBlocking { runNuXmv(modules, smvFile, logFile) }

        if (r) {
            info("$lp Equality proven")
        } else {
            info("$lp Equality not proven")
        }

        return r
    }

    private fun glueWithMiter(
        oldFrame: Frame,
        newFrame: Frame,
        old: SMVModule,
        new: SMVModule,
        ctx: ReveContext,
    ): List<SMVModule> {
        val a = SmvReveBuilder(oldFrame, newFrame, old, new, ctx)
        a.run()
        return a.modules
    }

    private fun smv(frame: Frame, state: SymbolicState = symbex(frame)): SMVModule {
        val moduleBuilder = ModuleBuilder(
            frame.name.replace(".", "$"),
            frame.scope,
            state,
            true,
        )
        moduleBuilder.run()
        return moduleBuilder.module
    }

    private val abstractionRecursionProtection = HashSet<Pair<String, String>>()

    private fun proofBodyEquivalenceWithAbstraction(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx("proofBodyEquivalenceWithAbstraction", old, new)

        if (old.name.endsWith("_abstracted") && (new.name.endsWith("_abstracted"))) {
            info("$lp declined, recursion protection triggered")
            return false
        }

        abstractionRecursionProtection.add(old.name to new.name)

        if (disableProofBodyEquivalenceWithAbstraction) {
            info("$lp Skipped because `disableProofBodyEquivalenceWithAbstraction` is set")
            return false
        }

        val aa = callSitePairs.filter { (a, b) ->
            a.isPrefix(old.block.fqName) && b.isPrefix(new.block.fqName)
        }
        val oldAbstractedFrames = aa.map { (a, _) -> a }
        val newAbstractedFrames = aa.map { (_, b) -> b }

        val bodyEq = proofBodyEquivalenceWithAbstractionBody(old, new, ctx, oldAbstractedFrames, newAbstractedFrames)
        val sfEq = if (bodyEq) {
            proofBodyEquivalenceWithAbstractionSubFrames(old, new, ctx, oldAbstractedFrames, newAbstractedFrames)
        } else {
            false
        }
        // val bodyEq = body.await()
        // val sfEq = subframes.await()

        val r = bodyEq && sfEq
        if (r) {
            info("$lp Equality proven")
        } else {
            info("$lp Equality not proven; body: $bodyEq, subFrame: $sfEq")
        }

        return r
    }

    private fun proofBodyEquivalenceWithAbstractionBody(
        old: Frame,
        new: Frame,
        ctx: ReveContext = reveContextManager.get(old, new),
        oldAbstractedFrames: List<BlockStatement>,
        newAbstractedFrames: List<BlockStatement>,
    ): Boolean {
        val lp = logprfx("proofBodyEquivalenceWithAbstractionBody", old, new)

        if (disableProofBodyEquivalenceWithAbstractionBody) {
            info("$lp Skipped because `disableProofBodyEquivalenceWithAbstractionBody` is set")
            return false
        }

        if (oldAbstractedFrames.isEmpty() || newAbstractedFrames.isEmpty()) {
            info("$lp No abstraction known/allowed")
            return false
        }

        val (oldM, oldInput, oldOutput) = abstractFrames(old, oldAbstractedFrames)
        val (newM, newInput, newOutput) = abstractFrames(new, newAbstractedFrames)

        val ctxNew = ctx.clone()

        callSitePairs.filter { (a, b) ->
            a.isPrefix(old.block.fqName) && b.isPrefix(new.block.fqName)
        }.forEach { (a, b) ->
            // assertion of call
            val c = a.getCallCounter()
            val d = b.getCallCounter()
            ctxNew.outRelation.add(RelatedVariables(SVariable(c.name), SBinaryOperator.EQUAL, SVariable(d.name)))

            // add assertion of input
            val q = reveContextManager.get(a, b)
            if (q != null) {
                val assertInRel = q.completeInRel(a, b).rewrite(oldInput[a]!!, newInput[b]!!)
                ctxNew.outRelation.addAll(assertInRel)

                val assumeOutRel = q.completeOutRel(a, b).rewrite(oldOutput[a]!!, newOutput[b]!!)
                ctxNew.inRelation.addAll(assumeOutRel)
            }
        }

        info("$lp Add new regression verification contract")
        info("Frame ${oldM.block.repr()} to ${newM.block.repr()}")
        info("\tContext: ${ctxNew.condition.repr()}")
        info("\tInput-Relation: ${ctxNew.createInRelation(oldM.block, newM.block, "old", "new").repr()}")
        info("\tOutput-Relation: ${ctxNew.createOutRelation(oldM.block, newM.block, "old", "new").repr()}")

        // recursion
        info("$lp Recursion for proofing abstracted body")
        return proofEquivalence(oldM, newM, ctxNew)
    }

    private fun proofBodyEquivalenceWithAbstractionSubFrames(
        old: Frame,
        new: Frame,
        ctx: ReveContext = reveContextManager.get(old, new),
        oldAbstractedFrames: List<BlockStatement>,
        newAbstractedFrames: List<BlockStatement>,
    ): Boolean {
        val lp = logprfx("proofBodyEquivalenceWithAbstractionSubFrames", old, new)
        if (disableProofBodyEquivalenceWithAbstractionSubFrames) {
            info("$lp Skipped because `disableProofBodyEquivalenceWithAbstractionSubFrames` is set")
            return false
        }

        val subFrames = callSitePairs.asSequence()
            .filter { (a, b) -> a.isTruePrefix(old.block.fqName) && b.isTruePrefix(new.block.fqName) }

        val names = subFrames.joinToString { (a, b) -> "${a.name}=${b.name}" }
        info("$lp Proving sub-frames: $names")

        val ctxEqual = subFrames.all { (cOld, cNew) ->
            // async
            proofEquivalence(
                createFrame(cOld, oldProgram.complete.scope),
                createFrame(cNew, newProgram.complete.scope),
            )
        }

        /*var ret = true
        for (deferred in ctxEqual) {
            if (!ret) {
                deferred.cancel("Because!")
                continue
            }
            ret = ret && !deferred //!deferred.await()
        }*/
        val ret = ctxEqual
        if (ret) {
            info("$lp proved equality of subframes")
        } else {
            info("$lp disproved equality of subframes")
        }

        return ret
    }

    fun proofBodyEquivalenceSource(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx("proofBodyEquivalenceSource", old, new)
        if (disableProofBodyEquivalenceSource) {
            info("$lp Skipped because `disableProofBodyEquivalenceSource` is set")
            return false
        }
        if (!ctx.onlyEquivalence) {
            info("$lp not suitable for frames ${old.name} and ${new.name}")
            return false
        }

        val result = old.block == new.block
        if (result) {
            info("$lp Frame ${old.name} is syntactical equivalent to  ${new.name} ")
        } else {
            info("$lp Frame ${old.name} is *not* syntactical equivalent to  ${new.name}")
        }
        return result
    }

    /*suspend*/
    fun proofBodyEquivalenceSSA(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx("proofBodyEquivalenceSSA", old, new)
        if (disableProofBodyEquivalenceSSA) {
            info("$lp Skipped because `disableProofBodyEquivalenceSSA` is set")
            return false
        }

        if (!ctx.isPerfect) {
            info("$lp not suitable for frames ${old.name} and ${new.name}")
            return false
        }

        val oldSmv = symbex(old)
        val newSmv = symbex(new)

        val commonOutput = old.block.output.intersect(new.block.output.toSet())
        val outVars = commonOutput.associate { it.identifier to it.identifier }
        val r = oldSmv.equal(newSmv, outVars)
        if (r) {
            info("$lp Frame ${old.name} is equivalent to  ${new.name} in SSA-form ")
        } else {
            info("$lp Frame ${old.name} is *not* equivalent to  ${new.name} in SSA-form")
        }
        return r
    }

    /*suspend*/
    fun proofBodyEquivalenceSMT(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx("proofBodyEquivalenceSMT", old, new)
        if (disableProofBodyEquivalenceSMT) {
            info("$lp Skipped because `disableProofBodyEquivalenceSMT` is set")
            return false
        }
        info("$lp Proof equivalence of frames ${old.name} and ${new.name}")

        info("$lp Translate ${old.name} to SMT")
        val pfxOld = "O_"
        val pfxNew = "N_"
        val oldSmv = smt(old, oldProgram.complete.scope, pfxOld)

        info("$lp Translate ${new.name} to SMT")
        val newSmv = smt(new, newProgram.complete.scope, pfxNew)

        info("$lp Create assertion")
        /*
        val commontInputState =
                old.block.input.intersect(new.block.input) + old.block.state.intersect(new.block.state)
        val commonOutput = old.block.output.intersect(new.block.output)
         */

        val assertion = CodeWriter()

        val equalInputStateSmv = ctx.createInRelation(old.block, new.block, pfxOld, pfxNew) and ctx.condition
        val equalOutputStateSmv = ctx.createOutRelation(old.block, new.block, pfxOld, pfxNew)

        val equalInputState = smv2smt(equalInputStateSmv).toString()

        val equal = smv2smt(equalOutputStateSmv).toString()

        assertion.write("(assert (and $equalInputState))\n")
        assertion.write("(assert (not (and $equal)))\n")
        assertion.write("(check-sat)\n")
        val smtProblem = oldSmv + newSmv + assertion.stream

        val smtFile = file("${old.name}_${new.name}_equiv.smt")
        info("$lp Write SMT problem into $smtFile")

        // withContext(Dispatchers.IO) {
        smtFile.bufferedWriter().use { it.write(smtProblem) }
        // }

        info("$lp Run z3 for ${old.name}_${new.name}_equiv.smt")
        val r = runBlocking { SmtFacade.checkSmtSat(smtProblem) == SmtAnswer.UNSAT }

        info("$lp Result of z3 is $r for ${old.name}_${new.name}_equiv.smt")
        return r
    }

    //region helpers
    private val dtSTranslator = DefaultTypeTranslator.INSTANCE
    private val dtTranslator = DefaultS2STranslator()
    private val fnTranslator = DefaultS2SFunctionTranslator()

    fun smv2smt(expr: SMVExpr, prefix: String = ""): SExpr {
        val v = Smv2SmtVisitor(fnTranslator, dtTranslator, statePrefix = prefix)
        return expr.accept(v)
    }

    private fun smt(frame: Frame, e: Scope, prefix: String): String {
        val v = Smv2SmtVisitor(fnTranslator, dtTranslator, statePrefix = "")
        val out = CodeWriter()
        val state = symbex(frame)
        val inputVars = frame.block.input.map { it.identifier }
        val stateVars = frame.block.state.map { it.identifier }
        val outputVars = frame.block.output.map { it.identifier }

        e.variables.filter { it.name in inputVars || it.name in outputVars || it.name in stateVars }
            .forEach {
                val dt = dtTranslator.translate(dtSTranslator.translate(it.dataType!!))
                out.write("(declare-const ${prefix}${it.name} $dt)\n")
            }

        val defs = state.getAllDefinitions()
        state.keys.filter { it.name in outputVars }
            .forEach {
                val e = state[it] ?: error("output variable not in defined in SSA.")
                val e1 = e.replaceExhaustive(defs)
                val expr = e1.accept(v)
                out.write("(assert (= ${prefix}${it.name} ${expr.toString(prefix)}))\n")
            }
        return out.stream.toString()
    }

    private fun SExpr.toString(varPrefix: String): String = when (this) {
        is SSymbol ->
            if (!text.startsWith("#")) {
                "${varPrefix}${this.text}"
            } else {
                toString()
            }
        is SList -> {
            val args = if (list.isNotEmpty()) {
                list.drop(1).joinToString(" ") { it.toString(varPrefix) }
            } else {
                ""
            }
            "(${list.first()} $args)"
        }
        else -> toString()
    }

    private fun symbex(frame: Frame, useDefs: Boolean = false): SymbolicState = if (!useDefs) {
        smvCache.computeIfAbsent(frame) { SymbExFacade.evaluateStatements(frame.block.statements, frame.scope, false) }
    } else {
        SymbExFacade.evaluateStatements(frame.block.statements, frame.scope, false)
    }

    private suspend fun runNuXmv(modules: List<SMVModule>, smvFile: File, logFile: File): Boolean {
        smvFile.bufferedWriter().use {
            val p = SMVPrinter(CodeWriter(it))
            modules.forEach { it.accept(p) }
        }

        info("runNuXmv: Run solver on $smvFile")
        val nuxmv = NuXMVProcess(smvFile, xmvCommandFile)
        nuxmv.outputFile = logFile
        val result = nuxmv.call()
        info("runNuXmv: Solver finished for $smvFile with $result")
        return when (result) {
            NuXMVOutput.Verified -> true
            is NuXMVOutput.Error -> error("runNuXmv: Error in SMV file: $smvFile")
            is NuXMVOutput.Cex -> false
        }
    }

    val xmvIc3Commands = listOf(
        "set default_trace_plugin 6",
        "read_model",
        "flatten_hierarchy",
        "show_vars",
        "encode_variables",
        "build_boolean_model",
        "check_invar_ic3",
        "quit",
    )
    val xmvCommandFile by lazy {
        val f = file("ic3.xmv")
        info("Create nuXmv command file `$f'")
        f.bufferedWriter().use { fw -> xmvIc3Commands.joinTo(fw, "\n") }
        f
    }
    //endregion

    //region symbolic execution with abstraction
    var uniqueCnt = 0
    fun abstractFrames(
        exec: Frame,
        abstractedBlocks: List<BlockStatement>,
    ): Triple<Frame, HashMap<BlockStatement, Map<String, String>>, HashMap<BlockStatement, Map<String, String>>> {
        val (abstracted, inputs, outputs) =
            createProgramWithAbstraction(exec, abstractedBlocks)

        file("${exec.block.name}_abstracted_${++uniqueCnt}.st").bufferedWriter()
            .use {
                IEC61131Facade.printTo(
                    it,
                    ProgramDeclaration(exec.name, exec.scope, StatementList(abstracted)),
                    true,
                )
            }
        val f = Frame(abstracted, exec.scope)
        abstracted.fqName = exec.block.fqName + "_abstracted"
        return Triple(f, inputs, outputs)
    }

    private fun createProgramWithAbstraction(a: Frame, abstractedInvocation: List<BlockStatement>) =
        rewriteInvocation(a, abstractedInvocation)

    fun rewriteInvocation(
        a: Frame,
        abstractedInvocation: List<BlockStatement>,
    ): Triple<
        BlockStatement,
        HashMap<BlockStatement, Map<String, String>>,
        HashMap<BlockStatement, Map<String, String>>,
        > {
        val new = a.block.clone()
        val scope = a.scope.copy()

        // foreach reference create a call counter
        abstractedInvocation.distinctBy { it.fqName }.forEach {
            val prefix = it.getCallCounter()
            val sr = SymbolicReference(prefix.name)
            new.statements.add(0, AssignmentStatement(sr, IntegerLit(USINT, BigInteger.ZERO)))
            scope.add(prefix)
        }

        val inputs = HashMap<BlockStatement, Map<String, String>>()
        val outputs = HashMap<BlockStatement, Map<String, String>>()

        abstractedInvocation.sortedBy { it.fqName }.forEach {
            val prefix = it.fqName.replace('.', '$')
            val rewriter = InvocationRewriter(prefix, scope, it)
            new.statements = new.statements.accept(rewriter) as StatementList
            inputs[it] = rewriter.inputs
            outputs[it] = rewriter.outputs
            // new.statements.add(0, "${prefix}_ccnt" assignTo IntegerLit(USINT, 0.toBigInteger()))}
        }
        return Triple(new, inputs, outputs)
    }
//endregion

    //region helpers
    private fun file(s: String) = File(outputFolder, s)
    private fun logprfx(method: String, a: Frame, b: Frame): String = "$method(${a.name},${b.name}): "
//endregion
}

class StopWatch {
    private val data = TreeMap<String, Long>()
    fun time(name: String, function: () -> Unit) {
        val start = System.currentTimeMillis()
        function()
        val end = System.currentTimeMillis()
        data[name] = (end - start)
    }

    override fun toString(): String = data.toString()
}

private fun List<RelatedVariables>.rewrite(
    oldMap: Map<String, String>,
    newMap: Map<String, String>,
): Collection<RelatedVariables> {
    val oldRename = VariableReplacer(oldMap.asSmv())
    val newRename = VariableReplacer(newMap.asSmv())

    return map { (o, op, n) ->
        RelatedVariables(o.accept(oldRename) as SMVExpr, op, n.accept(newRename) as SMVExpr)
    }
}

private fun Map<String, String>.asSmv(): Map<SMVExpr, SMVExpr> = map { (a, b) -> SVariable(a) to SVariable(b) }.toMap()

private fun BlockStatement.getCallCounter(): VariableDeclaration {
    val name = "${fqName.replace('.', '$')}_ccnt"
    return VariableDeclaration(name, VariableDeclaration.OUTPUT or TYPE_COUNTER, USINT)
}

private class SmvReveBuilder(
    val oldFrame: Frame,
    val newFrame: Frame,
    val old: SMVModule,
    val new: SMVModule,
    val ctx: ReveContext,
) {
    val main = SMVModule("main")
    val modules = listOf(main, old, new)

    private fun instantiateModule(name: String, mod: SMVModule) {
        val inputVars = mod.moduleParameters.map {
            SVariable("$name\$${it.name}", it.dataType!!)
        }
        main.inputVars.addAll(inputVars)
        val modVar = SVariable(name, ModuleType(mod.name, inputVars))
        main.stateVars.add(modVar)
    }

    fun run() {
        instantiateModule("old", old)
        instantiateModule("new", new)

        val premise = SVariable.create("__premise__").asBool()
        main.stateVars.add(premise)
        main.initAssignments.add(SAssignment(premise, SLiteral.TRUE))

        val inputRelated = ctx.createInRelation(
            oldFrame.block,
            newFrame.block,
            "old",
            "new",
        ) and ctx.condition

        val outputRelated = ctx.createOutRelation(
            oldFrame.block,
            newFrame.block,
            "old",
            "new",
        )

        main.nextAssignments.add(SAssignment(premise, premise and inputRelated))
        main.invariantSpecs.add(premise implies outputRelated)

        /*for ((fst, snd) in output) {
            val eq = SVariable.bool("eq_${fst.name}_${snd.name}")
            val old = fst.prefix(oldPrefix)
            val new = snd.prefix(newPrefix)
            module.definitions[eq] = old.equal(new)
            list.add(eq)
        }
         */
    }
}

private class InvocationRewriter(val prefix: String, val scope: Scope, val toBeReplaced: BlockStatement) : AstMutableVisitor() {

    val inputs = hashMapOf<String, String>()
    val outputs = hashMapOf<String, String>()

    override fun visit(blockStatement: BlockStatement): Any {
        if (blockStatement != toBeReplaced) return super.visit(blockStatement)
        val list = StatementList()

        val cnt = SymbolicReference(prefix + "_ccnt")
        val counterIncr = AssignmentStatement(cnt, cnt plus IntegerLit(USINT, BigInteger.ONE))
        list += counterIncr

        // Inputs
        val instanceName = blockStatement.fqName
            .removeSuffix(".${blockStatement.name}")
            .replace('.', '$')

        val prefix = blockStatement.repr().replace('.', '$')
        val inputsAssign =
            blockStatement.input.map {
                val n = it.identifier
                val new = "$prefix$${it.identifier}"
                val vdOut = scope.getVariable(it)
                val inputName = "${new}__input"
                scope.add(VariableDeclaration(inputName, 0 or TYPE_INPUT_FUNCTION_BLOCK, vdOut.dataType!!))
                inputs[n] = inputName
                inputName assignTo n
            }

        val randomOutput = blockStatement.output.map {
            val n = it.identifier
            val new = "$prefix$${it.identifier}"
            val vdOut = scope.getVariable(it)
            val outputName = "${new}__random"
            scope.add(VariableDeclaration(outputName, 0 or TYPE_OUTPUT_FUNCTION_BLOCK, vdOut.dataType!!))
            outputs[n] = outputName
            n assignTo outputName
        }
        list.addAll(inputsAssign)
        list.addAll(randomOutput)
        return list
    }
}

/**
 * Equality of two SymbolicStates is defined by the equality between all given output variables,
 * and the used input and state variables.
 *
 * All terms variables must be equal w.r.t. to their name.
 */
private fun SymbolicState.equal(otherState: SymbolicState, outputVariables: Map<String, String>): Boolean {
    val (r, stateMap) = InferEqualMod(this, otherState, outputVariables).run()
    return r && stateMap.all { (a, b) -> a == b }
}

private class InferEqualMod(
    val state1: SymbolicState,
    val state2: SymbolicState,
    val outputVariables: Map<String, String>,
) {

    val otherVariables = HashMap<String, String>()
    val defs1 = state1.getAllDefinitions()
    val defs2 = state2.getAllDefinitions()

    val cache = HashMap<Pair<SMVExpr?, SMVExpr?>, Boolean>()
    fun equalExprMemoized(a: SMVExpr?, b: SMVExpr?): Boolean {
        val key = a to b
        return if (key !in cache) {
            val r = equalExpr(a, b)
            cache[key] = r
            r
        } else {
            cache[key]!!
        }
    }

    fun equalExpr(a: SMVExpr?, b: SMVExpr?): Boolean = when {
        a == null && b == null -> true
        a is SBinaryExpression && b is SBinaryExpression ->
            a.operator == b.operator && equalExprMemoized(a.left, b.left) && equalExprMemoized(a.right, b.right)
        a is SUnaryExpression && b is SUnaryExpression ->
            a.operator == b.operator && equalExprMemoized(a.expr, b.expr)
        a is SLiteral -> a == b // just equality of values
        a is SVariable && b is SVariable -> { // crucial case
            if (a.name in outputVariables) {
                // if a is an output variable, then it should be equals to specified variable
                b.name == outputVariables[a.name]
            } else if (a in defs1 && b in defs2) {
                // Variables are definition, then go further
                equalExprMemoized(defs1[a]!!, defs2[b]!!)
            } else if ((a in defs1 && b !in defs2) || (a !in defs1 && b in defs2)) {
                // One of the variables are a definition but the other not.
                false
            } else if (a.name in otherVariables) {
                // a is a state/input variable, then it should be equal to previous match
                b.name == otherVariables[a.name]!!
            } else {
                // a is a state/input variable, but there is no previous match, store it.
                otherVariables[a.name] = b.name
                true
            }
        }
        a is SFunction && b is SFunction ->
            a.name == b.name &&
                a.arguments.size == b.arguments.size &&
                a.arguments.mapIndexed { idx, expr -> equalExprMemoized(expr, b.arguments[idx]) }.all { it }
        a is SQuantified && b is SQuantified ->
            // equal if same operator, and same quantified formulae
            a.operator == b.operator &&
                a.quantified.size == b.quantified.size &&
                a.quantified.mapIndexed { idx, expr -> equalExprMemoized(expr, b.quantified[idx]) }.all { it }
        a is SCaseExpression && b is SCaseExpression ->
            a.cases.size == b.cases.size &&
                a.cases.mapIndexed { idx, expr ->
                    val (cond, then) = expr
                    val (cond2, then2) = b.cases[idx]
                    return equalExprMemoized(cond, cond2) && equalExprMemoized(then, then2)
                }.all { it }
        else -> true
    }

    fun run(): Pair<Boolean, HashMap<String, String>> {
        val r = outputVariables.all { (a, b) -> equalExpr(state1[a], state2[b]) }
        return r to otherVariables
    }
}

private fun BlockStatement.isTruePrefix(prefix: String) = fqName.startsWith(prefix + ".")

private fun BlockStatement.isPrefix(prefix: String): Boolean = fqName.startsWith(prefix)

class ProcessRunner(
    val commandLine: Array<String>,
    val stdin: File,
    var workingDirectory: File = File("."),
    var stdoutFile: File = File(workingDirectory, "stdout.log"),
) {
    suspend fun call(): String {
        val pb = ProcessBuilder(*commandLine)
            .directory(workingDirectory)
            .redirectErrorStream(true)
            .redirectOutput(stdoutFile)
            .redirectInput(stdin)
        return withContext(Dispatchers.IO) {
            val process = pb.start()
            // destroy the sub-process, if java is killed
            Runtime.getRuntime().addShutdownHook(Thread { if (process.isAlive) process.destroyForcibly() })
            process.waitFor()
            stdoutFile.bufferedReader().readText()
        }
    }
}

var nuxmvDefaultPath = "nuXmv"

class NuXMVProcess(var moduleFile: File, val commandFile: File) {
    var executablePath = nuxmvDefaultPath
    var workingDirectory = moduleFile.parentFile
    var outputFile = File(workingDirectory, "nuxmv.log")
    var result: NuXMVOutput? = null
    var outputParser: NuXMVOutputParser = ::parseXmlOutput

    suspend fun call(): NuXMVOutput {
        workingDirectory.mkdirs()
        val commands = arrayOf(executablePath, "-int", moduleFile.absolutePath)
        try {
            info(commands.joinToString(" "))
            // info("Working Directory: {}", workingDirectory)
            // info("Result in {}", outputFile)
            val pr = ProcessRunner(
                commands,
                commandFile,
                workingDirectory,
                outputFile,
            )
            val output = pr.call()
            result = outputParser(output)
            return result!!
        } catch (e: InterruptedException) {
            e.printStackTrace()
        }
        return NuXMVOutput.Error()
    }
}

private fun printStatistic(new: Frame): String {
    val code = IEC61131Facade.print(new.block, false)
    val loc = code.count { it == '\n' }
    val inVars = new.block.input.size
    val outVars = new.block.output.size
    val stateVars = new.block.state.size
    return "(LoC:$loc) (Vars: [$stateVars] ($inVars) => ($outVars))"
}