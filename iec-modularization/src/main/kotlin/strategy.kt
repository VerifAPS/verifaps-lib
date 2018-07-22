package edu.kit.iti.formal.automation.modularization

import edu.kit.iti.formal.automation.rvt.RegressionVerification
import edu.kit.iti.formal.automation.st.ast.Invoked
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.07.18)
 */

interface ProofStrategy {
    fun createTask(a: ProgramDeclaration,
                   b: ProgramDeclaration,
                   abstractAllowed: CallSiteMapping): Pred
}

class DefaultStrategy(val mp: ModularProver) : ProofStrategy {
    override fun createTask(a: ProgramDeclaration, b: ProgramDeclaration, abstractAllowed: CallSiteMapping): Pred {
        return equalBodiesUnderAbstraction(a, b, abstractAllowed, arrayListOf(a.name), arrayListOf(b.name))
    }

    fun createEquivalencePO(a: PouExecutable, b: PouExecutable, abstractAllowed: CallSiteMapping,
                            oP: List<String>, oN: List<String>): RegressionVerification {
        val aa = abstractAllowed.filter { (a, b) -> a.isPrefix(oP) && b.isPrefix(oN) }

        val oldAbstractedInvocation = aa.map { (a, _) -> a }
        val newAbstractedInvocation = aa.map { (_, b) -> b }

        val old = evaluateProgramWithAbstraction(a, oldAbstractedInvocation)
        val new = evaluateProgramWithAbstraction(b, newAbstractedInvocation)
        val rv = RegressionVerification(old, new)
        rv.run()
        return rv
    }

    private fun equalBodiesUnderAbstraction(a: PouExecutable, b: PouExecutable, abstractAllowed: CallSiteMapping,
                                            oldPrefix: List<String>,
                                            newPrefix: List<String>): Pred {
        val sc = SourceEqualTask(a, b)
        val module: RegressionVerification = createEquivalencePO(a, b, abstractAllowed, oldPrefix, newPrefix)
        val smvFile = File(mp.args.outputFolder, "${a.name}_${b.name}.smv")
        val logFile = File(mp.args.outputFolder, "${a.name}_${b.name}.log")
        smvFile.bufferedWriter().use(module::writeTo)
        val xmv = NuXmvTask(smvFile, logFile, "Equality of ${a.name} against ${b.name}")

        // find call sites
        val callSiteTask: List<Pred> =
                abstractAllowed.filter { (a, b) -> a.isPrefix(oldPrefix) && b.isPrefix(newPrefix) }
                        .map { (cOld, cNew) ->
                            val oldFb = (cOld.statement.invoked as Invoked.FunctionBlock).fb
                            val newFb = (cNew.statement.invoked as Invoked.FunctionBlock).fb

                            val oP = oldPrefix + cOld.statement.callee.identifier
                            val nP = newPrefix + cNew.statement.callee.identifier

                            equalBodiesUnderAbstraction(oldFb, newFb, abstractAllowed, oP, nP)
                        }


        return ((sc or xmv) and { callSiteTask.all { it() } }) or equalBodiesFull(a, b, oldPrefix, newPrefix)
    }

    private fun equalBodiesFull(a: PouExecutable, b: PouExecutable, oP: List<String>, oN: List<String>): Pred {
        //val closedPrograms = closedBody(a.stBody!!) && closedBody(b.stBody!!)
        val module: RegressionVerification = createEquivalencePO(a, b, listOf(), oP, oN)
        val smvFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.smv")
        val logFile = File(mp.args.outputFolder, "${a.name}_${b.name}_full.log")
        smvFile.bufferedWriter().use(module::writeTo)
        val xmv = NuXmvTask(smvFile, logFile, "Equality of ${a.name} against ${b.name}")
        return xmv
    }
}
