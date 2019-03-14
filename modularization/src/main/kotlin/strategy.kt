package edu.kit.iti.formal.automation.modularization

import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.Semaphore

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

abstract class ProofTask {
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

    abstract protected fun prove(): Boolean?
    abstract protected fun init()
}


interface VCGGenerator {
    fun generate(mp: ModularProver): Collection<ProofTask>
}
interface EqualityStrategy {}
interface ParameterCheck {}
interface ActivationCheck {}

// class DefaultEqualityStrategy(val mp: ModularProver) {
// fun createTask(a: ProgramDeclaration, b: ProgramDeclaration, abstractAllowed: CallSiteMapping)
// : ProofTask =
// equalBodiesUnderAbstraction(a, b, abstractAllowed, arrayListOf(a.name), arrayListOf(b.name))
//
// fun createEquivalencePO(a: PouExecutable, b: PouExecutable, abstractAllowed: CallSiteMapping,
// oP: List<String>, oN: List<String>): RegressionVerification {
// val aa = abstractAllowed.filter { (a, b) -> a.isPrefix(oP) && b.isPrefix(oN) }
//
// val oldAbstractedInvocation = aa.map { (a, _) -> a }
// val newAbstractedInvocation = aa.map { (_, b) -> b }
//
// val old = evaluateProgramWithAbstraction(a, oldAbstractedInvocation)
// val new = evaluateProgramWithAbstraction(b, newAbstractedInvocation)
// val rv = RegressionVerification(old, new)
// rv.run()
// return rv
// }
//
// private fun equalBodiesUnderAbstraction(a: PouExecutable, b: PouExecutable,
// abstractAllowed: CallSiteMapping,
// oldPrefix: List<String>,
// newPrefix: List<String>): Pred {
// val sc = SourceEqualTask(a, b)
// val module: RegressionVerification = createEquivalencePO(a, b, abstractAllowed, oldPrefix, newPrefix)
// val smvFile = File(mp.args.outputFolder, "${a.name}_${b.name}.smv")
// val logFile = File(mp.args.outputFolder, "${a.name}_${b.name}.log")
// smvFile.bufferedWriter().use(module::writeTo)
// val xmv = NuXmvTask(smvFile, logFile, "Equality of ${a.name} against ${b.name}")
//
// // find call sites
// val callSiteTask: List<Pred> =
// abstractAllowed.filter { (a, b) -> a.isPrefix(oldPrefix) && b.isPrefix(newPrefix) }
// .map { (cOld, cNew) ->
// val oldFb = (cOld.statement.invoked as Invoked.FunctionBlock).fb
// val newFb = (cNew.statement.invoked as Invoked.FunctionBlock).fb
//
// val oP = oldPrefix + cOld.statement.callee.identifier
// val nP = newPrefix + cNew.statement.callee.identifier
//
// equalBodiesUnderAbstraction(oldFb, newFb, abstractAllowed, oP, nP)
// }
//
//
// return ((sc or xmv) and { callSiteTask.all { it() } }) or equalBodiesFull(a, b, oldPrefix, newPrefix)
// }
//
// private fun equalBodiesFull(a: PouExecutable, b: PouExecutable, oP: List<String>, oN: List<String>): Pred {
// //val closedPrograms = closedBody(a.stBody!!) && closedBody(b.stBody!!)
// val module: RegressionVerification = createEquivalencePO(a, b, listOf(), oP, oN)
// val smvFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.smv")
// val logFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.log")
// smvFile.bufferedWriter().use(module::writeTo)
// val xmv = NuXmvTask(smvFile, logFile, "Equality of ${a.name} against ${b.name}")
// return xmv
// }
// }