@file:Suppress("MemberVisibilityCanBePrivate")

package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.modularization.ModFacade.createFrame
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.smt.*
import edu.kit.iti.formal.automation.st.ast.BlockStatement
import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SSymbol
import edu.kit.iti.formal.smt.SmtAnswer
import edu.kit.iti.formal.smt.SmtFacade
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.info
import kotlinx.coroutines.*
import java.io.File

/*
typealias ProofTask = suspend () -> Boolean

enum class ProofTaskState {
    /**
     * Uninitialized proof state.
     * Before VCG files (smv, smt) are generated...
     */
    UNPREPARED,

    /**
     * Waiting on other proof tasks
     */
    BLOCKED,

    /**
     * waiting on a free slot in the executor
     */
    PENDING,

    /**
     * Work in progress
     */
    RUNNING,

    /**
     * finished with a valid
     */
    FINISHED_VALID,

    /**
     * finished with a counter example
     */
    FINISHED_INVALID,

    /**
     * finished, property is valid and does not need to be checked.
     */
    FINISHED_SKIPPED,

    /**
     * error state, proof invalid, ...
     */
    ERROR
}

class ProofExecutor(val tasks: List<ProofTask>,
                    val executor: ExecutorService = Executors.newFixedThreadPool(4)) {
    private val semaphore = Semaphore(1 - tasks.size, false)

    private val displayThread = Thread {
        while (true) {
            if (Thread.currentThread().isInterrupted) break
            display()
            val finished = tasks.sumBy { if (it.finished) 1 else 0 }
            println("Finished: $finished")
            if (finished == tasks.size) break
            Thread.sleep(100)
        }
    }

    fun display() {
        print(String.format("\u001b[%dA", 1 + tasks.size)) // Move up
        val eraseLine = "\u001b[2K" // Erase line content
        tasks.forEach {
            println("$eraseLine${it.desc}\t\t${it.state}\t${it.time}")
        }
    }

    private fun runPossible() {
        tasks.forEach {
            if (it.startable) {
                it.status = ProofTaskState.PENDING
                executor.submit {
                    it.run()
                    runPossible()
                    semaphore.release()
                }
            }
        }
    }

    fun start() {
        tasks.forEach { it.prepare() }
        displayThread.start()
        runPossible()
        semaphore.acquire()
        displayThread.interrupt()
        /*do {
            if (barrier.isBroken) {
                executor.shutdownNow()
                break
            }
            barrier.await(10, TimeUnit.MILLISECONDS)
        } while (barrier.numberWaiting <= tasks.size)*/
    }
}

/*abstract class ProofTask {
    var time: Long = -1
    var desc: String = "<anonym>"
    internal var status: ProofTaskState = ProofTaskState.UNPREPARED
    val predecessors = arrayListOf<ProofTask>()

    val state
        get() = status

    val startable: Boolean
        get() = !finished && predecessors.all { it.finished }

    val finished: Boolean
        get() = state == ProofTaskState.FINISHED_SKIPPED || state == ProofTaskState.FINISHED_VALID || state == ProofTaskState.FINISHED_INVALID

    fun prepare() {
        init()
        status = ProofTaskState.BLOCKED
    }

    fun run() {
        status = ProofTaskState.RUNNING
        try {
            val timeBefore = System.currentTimeMillis()
            val r = prove()
            time = System.currentTimeMillis() - timeBefore
            status = when (r) {
                null -> ProofTaskState.FINISHED_SKIPPED
                true -> ProofTaskState.FINISHED_VALID
                false -> ProofTaskState.FINISHED_INVALID
            }
        } catch (e: Exception) {
            status = ProofTaskState.ERROR
        }
    }

    protected abstract fun prove(): Boolean?
    protected abstract fun init()
}
*/
*/

data class Frame(val block: BlockStatement, val scope: Scope)

class DefaultEqualityStrategy(val mp: ModularProver) {
    val outputFolder = mp.args.outputFolder
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
        val oldInstance = old.block.originalInvoked.name
        val newInstance = new.block.originalInvoked.name
        return equivCache.any { (a, b, c) -> oldInstance == a && b == newInstance && ctx <= c }
    }

    private fun updateCache(old: Frame, new: Frame, ctx: ReveContext, equal: Boolean) {
        val oldInstance = old.block.originalInvoked.name
        val newInstance = new.block.originalInvoked.name
        if (equal && oldInstance != null && newInstance != null)
            equivCache.add(Triple(oldInstance, newInstance, ctx))
    }

    suspend fun proofBodyEquivalenceClassic(old: Frame, new: Frame, ctx: ReveContext): Boolean = coroutineScope {
        return@coroutineScope true
    }

    private suspend fun proofBodyEquivalenceWithAbstraction(old: Frame, new: Frame, ctx: ReveContext): Boolean =
            coroutineScope {
                val aa = callSitePairs.filter { (a, b) ->
                    a.isPrefix(old.block.fqName) && b.isPrefix(new.block.fqName)
                }
                val oldAbstractedFrames = aa.map { (a, _) -> a }
                val newAbstractedFrames = aa.map { (_, b) -> b }

                val body = async { proofBodyEquivalenceWithAbstractionBody(old, new, ctx, oldAbstractedFrames, newAbstractedFrames) }
                val subframes = async { proofBodyEquivalenceWithAbstractionSubFrames(old, new, ctx, oldAbstractedFrames, newAbstractedFrames) }
                body.await() && subframes.await()
            }

    /**
     *
     */
    private suspend fun proofBodyEquivalenceWithAbstractionBody(
            old: Frame, new: Frame, ctx: ReveContext,
            oldAbstractedFrames: List<BlockStatement>,
            newAbstractedFrames: List<BlockStatement>): Boolean = coroutineScope {
        val old = evaluateFrameWithAbstraction(old, oldAbstractedFrames)
        val new = evaluateFrameWithAbstraction(new, newAbstractedFrames)

        //TODO add assertion, build common model

        val smvFile = File(mp.args.outputFolder, "${old.name}_${new.name}.smv")
        val logFile = File(mp.args.outputFolder, "${old.name}_${new.name}.log")
        runNuXmv(smvFile, logFile)
    }

    /**
     *
     */
    private suspend fun proofBodyEquivalenceWithAbstractionSubFrames(
            old: Frame, new: Frame, ctx: ReveContext,
            oldAbstractedFrames: List<BlockStatement>,
            newAbstractedFrames: List<BlockStatement>): Boolean = coroutineScope {

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
        ret
    }

    /*val smvFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.smv")
    val logFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.log")
    smvFile.bufferedWriter().use(module::writeTo)
    info("Equality of ${a.name} against ${b.name}")
    return runNuXmv(smvFile, logFile)*/

    fun proofBodyEquivalenceSource(oldProgram: Frame, newProgram: Frame, ctx: ReveContext): Boolean {
        if (!ctx.onlyEquivalence) {
            info("proofBodyEquivalenceSSA -- not suitable for frames ${oldProgram.block.name} and ${newProgram.block.name}")
            return false
        }
        info("Check frame ${oldProgram.block.name} against ${newProgram.block.name}")
        val result = oldProgram.block == newProgram.block
        info("==> $result")
        return result
    }

    suspend fun proofBodyEquivalenceSSA(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        if (!ctx.onlyEquivalence) {
            info("proofBodyEquivalenceSSA -- not suitable for frames ${old} and ${new}")
            return false
        }

        val oldSmv = symbex(old)
        val newSmv = symbex(new)
        val reachedStateVariables = hashSetOf<SVariable>()

        val commonOutput = old.block.output.intersect(new.block.output)

        return commonOutput.all {
            oldSmv[it.identifier].equalModuloState(newSmv[it.identifier], oldSmv, newSmv)
        }
    }

    suspend fun proofBodyEquivalenceSMT(old: Frame, new: Frame, ctx: ReveContext): Boolean {
        val oldSmv = smt(old, oldProgram.complete.scope, "O_")
        val newSmv = smt(new, newProgram.complete.scope, "N_")
        val commonOutput = old.block.output.intersect(new.block.output)
        val assertion = CodeWriter()

        //TODO assertion.write(ctx.relation)
        //TODO assertion.write(ctx.condition)
        val equal = commonOutput.joinToString(" ") {
            val op = ctx.relationOf(it.identifier, it.identifier)
            "(${op.symbol()} O_${it} N_${it})"
        }
        assertion.write("(assert (not (and $equal))\n")
        assertion.write("(check-sat)\n")
        val smtProblem = oldSmv + newSmv + assertion
        return SmtFacade.checkSmtSat(smtProblem) == SmtAnswer.UNSAT
    }

    private fun smt(frame: Frame, e: Scope, prefix: String): String {
        val dtSTranslator = DefaultTypeTranslator()
        val dtTranslator = DefaultS2STranslator()
        val fnTranslator = DefaultS2SFunctionTranslator()

        val v = Smv2SmtVisitor(fnTranslator, dtTranslator)
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
        //define definition
        /*input.getAllDefinitions().forEach { t, e ->
            val type = dtTranslator.translate(e.dataType!!)
            val smt = e.accept(v)
            out.write("(define-const ${prefix}${t.name} $type $smt)\n"))
        }*/
        //assert next
        val defs: Map<SMVExpr, SMVExpr> = input.definitions
                .map { (a, b) -> (a as SMVExpr) to b.value!! }
                .toMap()
        input.keys.filter { it.name in outputVars }
                .forEach {
                    val e = input[it] ?: error("output variable not in defined in SSA.")
                    val e1 = e.replaceExhaustive(defs)
                    val expr = e1.accept(v)
                    expr.toString(prefix)
                    out.write("(assert (= ${prefix}${it.name} $expr))\n")
                }
        return out.stream.toString()
    }

    fun SExpr.toString(varPrefix: String) = when (this) {
        is SSymbol -> "${varPrefix}${this.text}"
        else -> toString()
    }

    private fun symbex(frame: Frame): SymbolicState = smvCache.computeIfAbsent(frame) {
        SymbExFacade.evaluateStatements(frame.block.statements, frame.scope)
    }

    private suspend fun runNuXmv(smvFile: File, logFile: File): Boolean {
        info("Run solver on $smvFile")
        val cmdFile = File(COMMAND_FILE)
        writeNuxmvCommandFile(NuXMVInvariantsCommand.IC3.commands as Array<String>, cmdFile)
        val nuxmv = NuXMVProcess(smvFile, cmdFile)
        nuxmv.outputFile = logFile
        val result = nuxmv.call()
        info("Solver finished for $smvFile with $result")
        return when (result) {
            NuXMVOutput.Verified -> true
            is NuXMVOutput.Error -> error("Error in SMV file: $smvFile")
            is NuXMVOutput.Cex -> false
        }
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
