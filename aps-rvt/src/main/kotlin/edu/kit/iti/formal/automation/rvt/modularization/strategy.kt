@file:Suppress("MemberVisibilityCanBePrivate")

package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
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
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
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
    val outputFolder = mp.outputFolder
    val callSitePairs = mp.callSitePairs

    val oldProgram = mp.oldProgram
    val newProgram = mp.newProgram
    val topLevelContext = mp.context

    val smvCache = HashMap<Frame, SymbolicState>()

    suspend fun proofEquivalenceTopLevel() =
            proofEquivalence(oldProgram.frame, newProgram.frame, topLevelContext)

    suspend fun proofEquivalence(old: Frame, new: Frame, ctx: ReveContext): Boolean {
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

    private val equivCache = arrayListOf<Triple<String, String, ReveContext>>()

    private fun checkCache(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx(old, new)
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
        val lp = logprfx(old, new)

        val oldInstance = old.block.originalInvoked.name
        val newInstance = new.block.originalInvoked.name
        if (equal && oldInstance != null && newInstance != null) {
            equivCache.add(Triple(oldInstance, newInstance, ctx))
            info("$lp Update cache with $oldInstance and $newInstance")
        }
    }

    suspend fun proofBodyEquivalenceClassic(old: Frame, new: Frame, ctx: ReveContext): Boolean = coroutineScope {
        val lp = logprfx(old, new)
        info("$lp Not implemented")
        TODO()
        return@coroutineScope true
    }

    private suspend fun proofBodyEquivalenceWithAbstraction(old: Frame, new: Frame, ctx: ReveContext): Boolean =
            coroutineScope {
                val lp = logprfx(old, new)

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
            old: Frame, new: Frame, ctx: ReveContext,
            oldAbstractedFrames: List<BlockStatement>,
            newAbstractedFrames: List<BlockStatement>): Boolean = coroutineScope {
        val lp = logprfx(old, new)

        val old = evaluateFrameWithAbstraction(old, oldAbstractedFrames)
        val new = evaluateFrameWithAbstraction(new, newAbstractedFrames)

        //TODO add assertion, build common model

        val smvFile = file("${old.name}_${new.name}.smv")
        val logFile = file("${old.name}_${new.name}.log")

        info("$lp Starting proof: $smvFile, $logFile")

        val r = runNuXmv(smvFile, logFile)

        r
    }

    /**
     *
     */
    private suspend fun proofBodyEquivalenceWithAbstractionSubFrames(
            old: Frame, new: Frame, ctx: ReveContext,
            oldAbstractedFrames: List<BlockStatement>,
            newAbstractedFrames: List<BlockStatement>): Boolean = coroutineScope {
        val lp = logprfx(old, new)

        val ctxEqual = callSitePairs.asSequence()
                .filter { (a, b) -> a.isPrefix(old.block.fqName) && b.isPrefix(new.block.fqName) }
                .map { (cOld, cNew) ->
                    async {
                        val subCtx = ctx //TODO create subCtx
                        return@async proofEquivalence(createFrame(cOld, oldProgram.complete.scope),
                                createFrame(cNew, newProgram.complete.scope), subCtx)
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
        val lp = logprfx(old, new)

        if (!ctx.onlyEquivalence) {
            info("$lp not suitable for frames ${old.name} and ${new.name}")
            return false
        }

        val result = old.block == new.block
        if (result) {
            info("$lp Frame ${old.name} is syntactical equivalent to  ${new.name} ")
        } else {
        }
        info("$lp Frame ${old.name} is *not* syntactical equivalent to  ${new.name}")
        return result
    }

    suspend fun proofBodyEquivalenceSSA(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx(old, new)
        if (!ctx.onlyEquivalence) {
            info("$lp not suitable for frames ${old} and ${new}")
            return false
        }

        val oldSmv = symbex(old)
        val newSmv = symbex(new)
        val reachedStateVariables = hashSetOf<SVariable>()

        val commonOutput = old.block.output.intersect(new.block.output)

        val r = commonOutput.all {
            oldSmv[it.identifier].equalModuloState(newSmv[it.identifier], oldSmv, newSmv)
        }
        if (r)
            info("$lp Frame ${old.name} is equivalent to  ${new.name} in SSA-form ")
        else
            info("$lp Frame ${old.name} is *not* equivalent to  ${new.name} in SSA-form")
        return r
    }

    suspend fun proofBodyEquivalenceSMT(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val lp = logprfx(old, new)

        info("$lp Proof equivalence of frames ${old.name} and ${new.name}")

        info("$lp Translate ${old.name} to SMT")
        val oldSmv = smt(old, oldProgram.complete.scope, "O_")

        info("$lp Translate ${new.name} to SMT")
        val newSmv = smt(new, newProgram.complete.scope, "N_")

        info("$lp Create assertion")
        val commontInputState =
                old.block.input.intersect(new.block.input) + old.block.state.intersect(new.block.state)
        val commonOutput = old.block.output.intersect(new.block.output)
        val assertion = CodeWriter()
        //TODO assertion.write(ctx.relation)
        //TODO assertion.write(ctx.condition)
        //TODO add equality of state and input
        val equalInputState = commontInputState.joinToString(" ") {
            val op = ctx.relationOf(it.identifier, it.identifier)
            "(${op.symbol()} O_${it.identifier} N_${it.identifier})"
        }

        val equal = commonOutput.joinToString(" ") {
            val op = ctx.relationOf(it.identifier, it.identifier)
            "(${op.symbol()} O_${it.identifier} N_${it.identifier})"
        }
        assertion.write("(assert (and $equalInputState))\n")
        assertion.write("(assert (not (and $equal)))\n")
        assertion.write("(check-sat)\n")
        val smtProblem = oldSmv + newSmv + assertion.stream

        val smtFile = file("${old.name}_${new.name}_equiv.smt")
        info("proofBodyEquivalenceSMT: Write SMT problem into $smtFile")
        smtFile.bufferedWriter().use { it.write(smtProblem) }

        info("proofBodyEquivalenceSMT: Run z3 for ${old.name}_${new.name}_equiv.smt")
        val r = SmtFacade.checkSmtSat(smtProblem) == SmtAnswer.UNSAT

        info("proofBodyEquivalenceSMT: Result of z3 is $r for ${old.name}_${new.name}_equiv.smt")
        return r
    }

    private fun smt(frame: Frame, e: Scope, prefix: String): String {
        val dtSTranslator = DefaultTypeTranslator()
        val dtTranslator = DefaultS2STranslator()
        val fnTranslator = DefaultS2SFunctionTranslator()

        val v = Smv2SmtVisitor(fnTranslator, dtTranslator, statePrefix = "")
        val out = CodeWriter()
        val input = symbex(frame)
        val inputVars = frame.block.input.map { it.identifier }
        val stateVars = frame.block.state.map { it.identifier }
        val outputVars = frame.block.output.map { it.identifier }

        e.variables.filter { it.name in inputVars || it.name in outputVars || it.name in stateVars }
                .forEach {
                    val dt = dtTranslator.translate(dtSTranslator.translate(it.dataType!!))
                    out.write("(declare-const ${prefix}${it.name} $dt)\n")
                }

        val defs = input.getAllDefinitions()
        input.keys.filter { it.name in outputVars }
                .forEach {
                    val e = input[it] ?: error("output variable not in defined in SSA.")
                    val e1 = e.replaceExhaustive(defs)
                    val expr = e1.accept(v)
                    out.write("(assert (= ${prefix}${it.name} ${expr.toString(prefix)}))\n")
                }
        return out.stream.toString()
    }

    fun SExpr.toString(varPrefix: String): String = when (this) {
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
        SymbExFacade.evaluateStatements(frame.block.statements, frame.scope)
    }

    private suspend fun runNuXmv(smvFile: File, logFile: File): Boolean {
        info("runNuXmv: Run solver on $smvFile")
        val cmdFile = file(COMMAND_FILE)
        writeNuxmvCommandFile(NuXMVInvariantsCommand.IC3.commands as Array<String>, cmdFile)
        val nuxmv = NuXMVProcess(smvFile, cmdFile)
        nuxmv.outputFile = logFile
        val result = nuxmv.call()
        info("runNuXmv: Solver finished for $smvFile with $result")
        return when (result) {
            NuXMVOutput.Verified -> true
            is NuXMVOutput.Error -> error("runNuXmv: Error in SMV file: $smvFile")
            is NuXMVOutput.Cex -> false
        }
    }

    //region
    fun createProgramWithAbstraction(a: Frame, abstractedInvocation: List<BlockStatement>) = rewriteInvocation(a, abstractedInvocation)

    fun evaluateFrameWithAbstraction(exec: Frame, abstractedBlocks: List<BlockStatement>): SMVModule {
        val abstracted =
                if (abstractedBlocks.isEmpty()) exec.block
                else createProgramWithAbstraction(exec, abstractedBlocks)
        //IEC61131Facade.resolveDataTypes(PouElements(elements.toMutableList()), exec.scope.topLevel)

        file("${exec.block.name}_abstracted.st").bufferedWriter()
                .use { IEC61131Facade.printTo(it, abstracted, true) }

        val se = SymbolicExecutioner(exec.scope.topLevel)
        exec.block.accept(se)

        val moduleBuilder = ModuleBuilder(exec.block.name, exec.scope, se.peek())
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
    private fun logprfx(a: Frame, b: Frame): String {
        val trace = Thread.currentThread().stackTrace
        val method = trace[trace.lastIndex - 1].methodName
        return "$method(${a.name},${b.name}): "
    }
    //endregion
}

class InvocationRewriter(val prefix: String,
                         val scope: Scope,
                         val toBeReplaced: BlockStatement) : AstMutableVisitor() {
    override fun visit(blockStatement: BlockStatement): Any {
        if (blockStatement != toBeReplaced) return super.visit(blockStatement)
        val list = StatementList()

        val cnt = SymbolicReference(prefix + "_ccnt")
        val counterIncr = AssignmentStatement(cnt, cnt plus IntegerLit(UINT, BigInteger.ONE))

        list += counterIncr

        //Inputs
        val prefix = blockStatement.repr().replace('.', '$')
        val inputsAssign =
                blockStatement.input.map {
                    val n = "$prefix$${it.identifier}"
                    val vdOut = scope.getVariable(it)
                    val inputName = "${n}__input"
                    scope.add(VariableDeclaration(inputName, 0 or TYPE_INPUT_FUNCTION_BLOCK, vdOut.dataType!!))
                    inputName assignTo n
                }

        val randomOutput = blockStatement.output.map {
            val n = "$prefix$${it.identifier}"
            val vdOut = scope.getVariable(it)
            val inputName = "${n}__random"
            scope.add(VariableDeclaration(inputName, 0 or TYPE_OUTPUT_FUNCTION_BLOCK, vdOut.dataType!!))
            n assignTo inputName
        }
        list.addAll(inputsAssign)
        list.addAll(randomOutput)

        //TODO remove state

        return list
    }
}

private fun SMVExpr?.equalModuloState(smvExpr: SMVExpr?, thisState: SymbolicState, otherState: SymbolicState): Boolean {
    if (this == null && smvExpr == null) return true
    if (this == smvExpr) return true
    //TODO This could be better, if we would not care about variable names of input and state vars
    // If x and y' are reached, assert that the states expr are equal.

    return false
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
