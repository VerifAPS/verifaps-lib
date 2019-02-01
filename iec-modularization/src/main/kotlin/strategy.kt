package edu.kit.iti.formal.automation.modularization

import java.util.concurrent.Executors
import java.util.concurrent.Semaphore
import java.util.concurrent.TimeUnit


enum class ProofState {
    UNPREPARED,
    BLOCKED,
    PENDING,
    RUNNING,
    FINISHED_VALID, FINISHED_INVALID, FINISHED_SKIPPED,
    ERROR
}

class ProofExecutor(topTask: ProofTask, done: () -> Unit = {}) {
    val tasks: List<ProofTask> = taskList(topTask)
    val semaphore = Semaphore(1- tasks.size, false)

    private fun taskList(topTask: ProofTask): List<ProofTask> {
        val seq = arrayListOf(topTask)
        topTask.predecessors.forEach { seq.addAll(taskList(it)) }
        return seq
    }

    private val displayThread = Thread {
        while (true) {
            display()
            val finished = tasks.sumBy { if (it.finished) 1 else 0 }
            println("Finished: $finished")
            if (finished == tasks.size) break
            Thread.sleep(100)
        }
    }
    private var executor = Executors.newFixedThreadPool(4)

    fun display() {
        print(String.format("\u001b[%dA", tasks.size)) // Move up
        print("\u001b[2K") // Erase line content
        tasks.forEach {
            println("${it.desc}\t\t${it.state}\t${it.time}")
        }
    }

    private fun runPossible() {
        tasks.forEach {
            if (it.startable) {
                it.status = ProofState.PENDING
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
    internal var status: ProofState = ProofState.UNPREPARED
    val predecessors = arrayListOf<ProofTask>()

    val state
        get() = status
    val startable: Boolean
        get() = !finished && predecessors.all { it.finished }
    val finished: Boolean
        get() = state == ProofState.FINISHED_SKIPPED || state == ProofState.FINISHED_VALID || state == ProofState.FINISHED_INVALID

    fun prepare() {
        init()
        status = ProofState.BLOCKED
    }

    fun run() {
        status = ProofState.RUNNING
        try {
            val timeBefore = System.currentTimeMillis()
            val r = prove()
            time = System.currentTimeMillis() - timeBefore
            status = when (r) {
                null -> ProofState.FINISHED_SKIPPED
                true -> ProofState.FINISHED_VALID
                false -> ProofState.FINISHED_INVALID
            }
        } catch (e: Exception) {
            status = ProofState.ERROR
        }
    }

    abstract protected fun prove(): Boolean?
    abstract protected fun init()
}


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