package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.st.ast.Invoked
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.util.info
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.withContext
import java.io.File

/*
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

typealias ProofTask = suspend () -> Boolean

class DefaultEqualityStrategy(val mp: ModularProver) {
    val outputFolder = mp.args.outputFolder
    val callSitePairs = mp.callSitePairs

    suspend fun equalityOf(oldProgram: ModularProgram, newProgram: ModularProgram)
            = equalBodiesUnderAbstraction(oldProgram.entry, newProgram.entry, listOf(), listOf())

    private suspend fun proofBodyEquivalenceXmv(a: PouExecutable, b: PouExecutable,
                                                csm: CallSiteMapping,
                                                oP: List<String>, oN: List<String>): Boolean {
        val aa = csm.filter { (a, b) -> a.isPrefix(oP) && b.isPrefix(oN) }
        val oldAbstractedInvocation = aa.map { (a, _) -> a }
        val newAbstractedInvocation = aa.map { (_, b) -> b }

        val old = evaluateProgramWithAbstraction(a, oldAbstractedInvocation)
        val new = evaluateProgramWithAbstraction(b, newAbstractedInvocation)
        //TODO add assertion

        val smvFile = File(mp.args.outputFolder, "${a.name}_${b.name}.smv")
        val logFile = File(mp.args.outputFolder, "${a.name}_${b.name}.log")

        //smvFile.bufferedWriter().use(module::writeTo)
        return runNuXmv(smvFile, logFile)
    }

    private suspend fun equalBodiesUnderAbstraction(
            a: PouExecutable, b: PouExecutable, oldPrefix: List<String>, newPrefix: List<String>): Boolean {

        val eqBody = proofBodyEquivalenceSource(a, b) || proofBodyEquivalenceXmv(
                a, b, callSitePairs, oldPrefix, newPrefix)

        if (eqBody) {
            // find call sites
            val ctxEqual = callSitePairs
                    .filter { (a, b) -> a.isPrefix(oldPrefix) && b.isPrefix(newPrefix) }
                    .all { (cOld, cNew) ->
                        val oldFb = (cOld.statement.invoked as Invoked.FunctionBlock).fb
                        val newFb = (cNew.statement.invoked as Invoked.FunctionBlock).fb
                        val oP = oldPrefix + cOld.statement.callee.identifier
                        val nP = newPrefix + cNew.statement.callee.identifier
                        equalBodiesUnderAbstraction(oldFb, newFb, oP, nP)
                    }
            if (ctxEqual)
                return true;
        }
        //fallback
        return equalBodiesFull(a, b, oldPrefix, newPrefix)
    }

    private suspend fun equalBodiesFull(a: PouExecutable, b: PouExecutable, oP: List<String>, oN: List<String>): Boolean {
        return proofBodyEquivalenceXmv(a, b, listOf(), oP, oN)
        /*val smvFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.smv")
        val logFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.log")
        smvFile.bufferedWriter().use(module::writeTo)
        info("Equality of ${a.name} against ${b.name}")
        return runNuXmv(smvFile, logFile)*/
    }

    private fun proofBodyEquivalenceSource(oldProgram: PouExecutable, newProgram: PouExecutable): Boolean {
        info("Check source code of ${oldProgram.name} against $newProgram.name")
        val result = oldProgram.stBody!! == newProgram.stBody!!
        info("==> $result")
        return result
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
