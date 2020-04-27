@file:Suppress("MemberVisibilityCanBePrivate")

package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
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
import kotlinx.coroutines.*
import java.io.File
import java.math.BigInteger

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

    val reveContextManager = mp.ctxManager

    val outputFolder = mp.outputFolder
    val callSitePairs = mp.callSitePairs

    val oldProgram = mp.oldProgram
    val newProgram = mp.newProgram
    val topLevelContext = mp.context

    val smvCache = HashMap<Frame, SymbolicState>()

    suspend fun proofEquivalenceTopLevel() =
            proofEquivalence(oldProgram.frame, newProgram.frame, topLevelContext)

    suspend fun proofEquivalence(old: Frame, new: Frame,
                                 ctx: ReveContext = reveContextManager.get(old, new)): Boolean {
        var equal = false
        if (!equal) equal = checkCache(old, new, ctx)
        if (!equal) equal = proofBodyEquivalenceSource(old, new, ctx)
        if (!equal) equal = proofBodyEquivalenceSSA(old, new, ctx)
        if (!equal) equal = proofBodyEquivalenceSMT(old, new, ctx)
        if (!equal) equal = proofBodyEquivalenceWithAbstraction(old, new, ctx)
        if (!equal) equal = proofBodyEquivalenceClassic(old, new, ctx)
        if (equal) updateCache(old, new, ctx, equal)
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
    suspend fun proofBodyEquivalenceClassic(old: Frame, new: Frame,
                                            ctx: ReveContext = reveContextManager.get(old, new))
            : Boolean = coroutineScope {
        val lp = logprfx("proofBodyEquivalenceClassic", old, new)

        if (disableProofBodyEquivalenceClassic) {
            info("$lp Skipped because `disableProofBodyEquivalenceClassic` is set")
            return@coroutineScope false
        }


        val oldSmv = smv(old)
        val newSmv = smv(new)

        val modules = glueWithMiter(old, new, oldSmv, newSmv, ctx)
        val smvFile = file("${old.name}_${new.name}.smv")
        val logFile = file("${old.name}_${new.name}.log")

        info("$lp Starting proof: $smvFile, $logFile")

        val r = runNuXmv(modules, smvFile, logFile)

        if (r) {
            info("$lp Equality proven")
        } else {
            info("$lp Equality not proven")
        }

        r
    }

    private fun glueWithMiter(oldFrame: Frame, newFrame: Frame, old: SMVModule, new: SMVModule, ctx: ReveContext): List<SMVModule> {
        val a = SmvReveBuilder(oldFrame, newFrame, old, new, ctx)
        a.run()
        return a.modules
    }

    private fun smv(frame: Frame, state: SymbolicState = symbex(frame)): SMVModule {
        val moduleBuilder = ModuleBuilder(frame.name, frame.scope, state)
        moduleBuilder.run()
        return moduleBuilder.module
    }

    private suspend fun proofBodyEquivalenceWithAbstraction(old: Frame, new: Frame, ctx: ReveContext): Boolean =
            coroutineScope {
                val lp = logprfx("proofBodyEquivalenceWithAbstraction", old, new)

                if (disableProofBodyEquivalenceWithAbstraction) {
                    info("$lp Skipped because `disableProofBodyEquivalenceWithAbstraction` is set")
                    return@coroutineScope false
                }

                val aa = callSitePairs.filter { (a, b) ->
                    a.isPrefix(old.block.fqName) && b.isPrefix(new.block.fqName)
                }
                val oldAbstractedFrames = aa.map { (a, _) -> a }
                val newAbstractedFrames = aa.map { (_, b) -> b }

                val body = async { proofBodyEquivalenceWithAbstractionBody(old, new, ctx, oldAbstractedFrames, newAbstractedFrames) }
                val subframes = async { proofBodyEquivalenceWithAbstractionSubFrames(old, new, ctx, oldAbstractedFrames, newAbstractedFrames) }
                val bodyEq = body.await()
                val sfEq = subframes.await()


                val r = bodyEq && sfEq
                if (r) {
                    info("$lp Equality proven")
                } else {
                    info("$lp Equality not proven; body: $bodyEq, subFrame: $sfEq")
                }

                r
            }

    /**
     *
     */
    private suspend fun proofBodyEquivalenceWithAbstractionBody(
            old: Frame, new: Frame, ctx: ReveContext = reveContextManager.get(old, new),
            oldAbstractedFrames: List<BlockStatement>,
            newAbstractedFrames: List<BlockStatement>): Boolean = coroutineScope {
        val lp = logprfx("proofBodyEquivalenceWithAbstractionBody", old, new)

        if (disableProofBodyEquivalenceWithAbstractionBody) {
            info("$lp Skipped because `disableProofBodyEquivalenceWithAbstractionBody` is set")
            return@coroutineScope false
        }

        val oldM = evaluateFrameWithAbstraction(old, oldAbstractedFrames)
        val newM = evaluateFrameWithAbstraction(new, newAbstractedFrames)
        val modules = glueWithMiter(old, new, oldM, newM, ctx)

        val smvFile = file("${old.name}_${new.name}.smv")
        val logFile = file("${old.name}_${new.name}.log")

        info("$lp Starting proof: $smvFile, $logFile")

        val r = runNuXmv(modules, smvFile, logFile)

        r
    }

    private suspend fun proofBodyEquivalenceWithAbstractionSubFrames(
            old: Frame, new: Frame, ctx: ReveContext = reveContextManager.get(old, new),
            oldAbstractedFrames: List<BlockStatement>,
            newAbstractedFrames: List<BlockStatement>): Boolean = coroutineScope {
        val lp = logprfx("proofBodyEquivalenceWithAbstractionSubFrames", old, new)
        if (disableProofBodyEquivalenceWithAbstractionSubFrames) {
            info("$lp Skipped because `disableProofBodyEquivalenceWithAbstractionSubFrames` is set")
            return@coroutineScope false
        }
        val ctxEqual = callSitePairs.asSequence()
                .filter { (a, b) -> a.isPrefix(old.block.fqName) && b.isPrefix(new.block.fqName) }
                .map { (cOld, cNew) ->
                    async {
                        return@async proofEquivalence(createFrame(cOld, oldProgram.complete.scope),
                                createFrame(cNew, newProgram.complete.scope))
                    }
                }

        var ret = true
        for (deferred in ctxEqual) {
            if (!ret) {
                deferred.cancel("Because!")
                continue
            }
            ret = ret && !deferred.await()
        }

        if (ret) {
            info("$lp proved equality of subframes")
        } else {
            info("$lp disproved equality of subframes")
        }

        ret
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

    suspend fun proofBodyEquivalenceSSA(old: Frame, new: Frame, ctx: ReveContext): Boolean = coroutineScope {
        val lp = logprfx("proofBodyEquivalenceSSA", old, new)
        if (disableProofBodyEquivalenceSSA) {
            info("$lp Skipped because `disableProofBodyEquivalenceSSA` is set")
            return@coroutineScope false
        }

        if (!ctx.onlyEquivalence) {
            info("$lp not suitable for frames ${old.name} and ${new.name}")
            return@coroutineScope false
        }

        val oldSmv = symbex(old)
        val newSmv = symbex(new)

        val commonOutput = old.block.output.intersect(new.block.output)
        val outVars = commonOutput.map { it.identifier to it.identifier }.toMap()
        val r = oldSmv.equal(newSmv, outVars)
        if (r)
            info("$lp Frame ${old.name} is equivalent to  ${new.name} in SSA-form ")
        else
            info("$lp Frame ${old.name} is *not* equivalent to  ${new.name} in SSA-form")
        r
    }

    suspend fun proofBodyEquivalenceSMT(old: Frame, new: Frame, ctx: ReveContext) = coroutineScope {
        val lp = logprfx("proofBodyEquivalenceSMT", old, new)
        if (disableProofBodyEquivalenceSMT) {
            info("$lp Skipped because `disableProofBodyEquivalenceSMT` is set")
            return@coroutineScope false
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
        /*commontInputState.joinToString(" ") {
    val op = ctx.relationBetween(it.identifier, it.identifier)
    "(${op.symbol()} O_${it.identifier} N_${it.identifier})"
        }*/

        val equal = smv2smt(equalOutputStateSmv).toString()/*commonOutput.joinToString(" ") {
            val op = ctx.relationBetween(it.identifier, it.identifier)
            "(${op.symbol()} O_${it.identifier} N_${it.identifier})"
        }*/

        assertion.write("(assert (and $equalInputState))\n")
        assertion.write("(assert (not (and $equal)))\n")
        assertion.write("(check-sat)\n")
        val smtProblem = oldSmv + newSmv + assertion.stream

        val smtFile = file("${old.name}_${new.name}_equiv.smt")
        info("proofBodyEquivalenceSMT: Write SMT problem into $smtFile")

        withContext(Dispatchers.IO) {
            smtFile.bufferedWriter().use { it.write(smtProblem) }
        }

        info("proofBodyEquivalenceSMT: Run z3 for ${old.name}_${new.name}_equiv.smt")
        val r = SmtFacade.checkSmtSat(smtProblem) == SmtAnswer.UNSAT

        info("proofBodyEquivalenceSMT: Result of z3 is $r for ${old.name}_${new.name}_equiv.smt")
        r
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
            if (!text.startsWith("#")) "${varPrefix}${this.text}"
            else toString()
        is SList -> {
            val args = if (list.isNotEmpty()) list.drop(1).joinToString(" ") { it.toString(varPrefix) }
            else ""
            "(${list.first()} $args)"
        }
        else -> toString()
    }

    private fun symbex(frame: Frame): SymbolicState = smvCache.computeIfAbsent(frame) {
        SymbExFacade.evaluateStatements(frame.block.statements, frame.scope, useDefinitions = false)
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
            "read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_boolean_model", "check_invar_ic3", "quit"
    )
    val xmvCommandFile by lazy {
        val f = file("ic3.xmv")
        info("Create nuXmv command file `$f'")
        f.bufferedWriter().use { fw -> xmvIc3Commands.joinTo(fw, "\n") }
        f
    }
    //endregion

    //region symbolic execution with abstraction
    fun createProgramWithAbstraction(a: Frame, abstractedInvocation: List<BlockStatement>) = rewriteInvocation(a, abstractedInvocation)

    fun evaluateFrameWithAbstraction(exec: Frame, abstractedBlocks: List<BlockStatement>): SMVModule {
        val abstracted =
                if (abstractedBlocks.isEmpty()) exec.block
                else createProgramWithAbstraction(exec, abstractedBlocks)
        //IEC61131Facade.resolveDataTypes(PouElements(elements.toMutableList()), exec.scope.topLevel)

        file("${exec.block.name}_abstracted.st").bufferedWriter()
                .use {
                    IEC61131Facade.printTo(
                            it,
                            ProgramDeclaration("<frame>", exec.scope, StatementList(abstracted)),
                            true)
                }
        val state = symbex(Frame(abstracted, exec.scope))
        val moduleBuilder = ModuleBuilder(exec.block.name, exec.scope, state)
        moduleBuilder.run()
        return moduleBuilder.module
    }

    fun rewriteInvocation(a: Frame, abstractedInvocation: List<BlockStatement>): BlockStatement {
        val new = a.block.clone()
        val scope = a.scope.copy()

        // foreach reference create a call counter
        abstractedInvocation.distinctBy { it.fqName }.forEach {
            val prefix = it.fqName.replace('.', '$')
            val sr = SymbolicReference(prefix + "_ccnt")
            new.statements.add(0, AssignmentStatement(sr, IntegerLit(INT, BigInteger.ZERO)))

            val vd = VariableDeclaration(sr.identifier, TYPE_COUNTER, UINT)
            scope.add(vd)
        }

        abstractedInvocation.forEach {
            val prefix = it.fqName.replace('.', '$')
            val rewriter = InvocationRewriter(prefix, scope, it)
            new.statements = new.statements.accept(rewriter) as StatementList
        }
        return new
    }
//endregion

    //region helpers
    private fun file(s: String) = File(outputFolder, s)
    private fun logprfx(method: String, a: Frame, b: Frame): String {
        return "$method(${a.name},${b.name}): "
    }
//endregion
}

private class SmvReveBuilder(
        val oldFrame: Frame, val newFrame: Frame,
        val old: SMVModule, val new: SMVModule, val ctx: ReveContext) {
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

        val inputRelated = ctx.createInRelation(oldFrame.block, newFrame.block,
                "old", "new") and ctx.condition

        val outputRelated = ctx.createOutRelation(oldFrame.block,
                newFrame.block, "old", "new")

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

private class InvocationRewriter(val prefix: String,
                                 val scope: Scope,
                                 val toBeReplaced: BlockStatement) : AstMutableVisitor() {
    override fun visit(blockStatement: BlockStatement): Any {
        if (blockStatement != toBeReplaced) return super.visit(blockStatement)
        val list = StatementList()

        val cnt = SymbolicReference(prefix + "_ccnt")
        val counterIncr = AssignmentStatement(cnt, cnt plus IntegerLit(UINT, BigInteger.ONE))

        list += counterIncr

        //Inputs
        val instanceName = blockStatement.fqName.removeSuffix(".${blockStatement.name}").replace('.','$')
        val prefix = blockStatement.repr().replace('.', '$')
        val inputsAssign =
                blockStatement.input.map {
                    val n = it.identifier
                    val new = "$prefix$${it.identifier}"
                    val vdOut = scope.getVariable(it)
                    val inputName = "${new}__input"
                    scope.add(VariableDeclaration(inputName, 0 or TYPE_INPUT_FUNCTION_BLOCK, vdOut.dataType!!))
                    inputName assignTo n
                }

        val randomOutput = blockStatement.output.map {
            val n = it.identifier
            val new = "$prefix$${it.identifier}"
            val vdOut = scope.getVariable(it)
            val outputName = "${new}__random"
            scope.add(VariableDeclaration(outputName, 0 or TYPE_OUTPUT_FUNCTION_BLOCK, vdOut.dataType!!))
            n assignTo outputName
        }
        list.addAll(inputsAssign)
        list.addAll(randomOutput)

        //TODO remove state
        //TODO add condition assertion

        return list
    }
}

/**
 * Equality of two SymbolicStates is defined by the equality between all given output variables,
 * and the used input and state variables.
 *
 * All terms variables must be equal w.r.t. to their name.
 */
private fun SymbolicState.equal(otherState: SymbolicState,
                                outputVariables: Map<String, String>): Boolean {

    val (r, stateMap) = InferEqualMod(this, otherState, outputVariables).run()
    return r && stateMap.all { (a, b) -> a == b }
}

private class InferEqualMod(
        val state1: SymbolicState,
        val state2: SymbolicState,
        val outputVariables: Map<String, String>) {

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
        } else cache[key]!!
    }

    fun equalExpr(a: SMVExpr?, b: SMVExpr?): Boolean =
            when {
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
                    a.name == b.name
                            && a.arguments.size == b.arguments.size
                            && a.arguments.mapIndexed { idx, expr -> equalExprMemoized(expr, b.arguments[idx]) }.all { it }
                a is SQuantified && b is SQuantified ->
                    // equal if same operator, and same quantified formulae
                    a.operator == b.operator
                            && a.quantified.size == b.quantified.size
                            && a.quantified.mapIndexed { idx, expr -> equalExprMemoized(expr, b.quantified[idx]) }.all { it }
                a is SCaseExpression && b is SCaseExpression ->
                    a.cases.size == b.cases.size
                            && a.cases.mapIndexed { idx, expr ->
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

private fun BlockStatement.isPrefix(prefix: String): Boolean {
    return fqName.startsWith(prefix)
}

class ProcessRunner(val commandLine: Array<String>,
                    val stdin: File,
                    var workingDirectory: File = File("."),
                    var stdoutFile: File = File(workingDirectory, "stdout.log")
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
            Runtime.getRuntime().addShutdownHook(
                    Thread { if (process.isAlive) process.destroyForcibly() })
            process.waitFor()
            stdoutFile.bufferedReader().readText()
        }
    }
}

class NuXMVProcess(var moduleFile: File, val commandFile: File) {
    var executablePath = "nuXmv"
    var workingDirectory = moduleFile.parentFile
    var outputFile = File(workingDirectory, "nuxmv.log")
    var result: NuXMVOutput? = null
    var outputParser: NuXMVOutputParser = ::parseXmlOutput

    suspend fun call(): NuXMVOutput {
        workingDirectory.mkdirs()
        val commands = arrayOf(executablePath, "-int", moduleFile.absolutePath)
        try {
            info(commands.joinToString(" "))
            info("Working Directory: {}", workingDirectory)
            info("Result in {}", outputFile)
            val pr = ProcessRunner(commands,
                    commandFile,
                    workingDirectory,
                    outputFile)
            val output = pr.call()
            result = outputParser(output)
            return result!!
        } catch (e: InterruptedException) {
            e.printStackTrace()
        }
        return NuXMVOutput.Error()
    }
}
