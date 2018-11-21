import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.smv.SMVAstDefaultVisitor
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.io.PrintWriter
import java.util.*
import java.util.concurrent.Callable

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.11.18)
 */
class AbstractInterpretationSfc(val sfcDiff: DifferenceSfc, val leftScope: Scope, val rightScope: Scope) : Runnable {
    val lattice = TaintEqLattice()
    val allVariables =
            TreeSet(leftScope.variables.map { it.name }
                    + rightScope.variables.map { it.name })

    override fun run() {
        var change: Boolean
        Console.info("Mark all variables as equals")
        var iter = 1
        markAllVariablesAsEquals()
        do {
            Console.info("$iter Iteration")
            val update = sfcDiff.states.values.map {
                val c = updateState(it)
                if (c)
                    Console.info("Next iteration will happen: ${it.name} changed!")
                c
            }
            change = update.any { it }
            Console.info("Change is $change.")
            iter++
        } while (change)
        //TODO Taint guards!
    }

    private fun updateState(it: DifferenceState): Boolean {
        val oldState = it.abstractVariable.toMap()
        val incomingNode = it.leftIncomingTransitions.keys + it.rightIncomingTransitions.keys

        val incomingTaint =
                if (incomingNode.isEmpty()) hashMapOf()
                else
                    incomingNode.map { it.abstractVariable }
                            .reduce { a, b ->
                                val c = a.toMutableMap()
                                c.putAll(b)
                                for (k in a.keys.intersect(b.keys)) {
                                    val t1 = a[k]!!
                                    val t2 = b[k]!!
                                    c[k] = lattice.cup(t1, t2)
                                }
                                c
                            }
        val variables = (it.rightAssignments.keys + it.leftAssignments.keys)
        variables.forEach { v ->
            val leftExpr = it.leftAssignments[v]
            val rightExpr = it.rightAssignments[v]
            val new = updateAssignment(incomingTaint, leftExpr, rightExpr)
            val old = it.abstractVariable[v]!!
            it.abstractVariable[v] = new
            if (new != old) {
                Console.info("Value changed in ${it.name} for $v.")
            }
        }

        return it.abstractVariable.any { (v, eq) -> eq != oldState[v] }
    }

    private fun updateAssignment(incomingTaint: MutableMap<String, TaintEq>,
                                 leftExpr: SMVExpr?,
                                 rightExpr: SMVExpr?): TaintEq {
        val equal = leftExpr == rightExpr
        if (equal) {
            val vars = leftExpr.getVariables()
            val varsEqual = vars.all { incomingTaint[it] == TaintEq.EQUAL }
            return if (varsEqual) TaintEq.EQUAL else TaintEq.NOT_EQUAL
        } else {
            return TaintEq.NOT_EQUAL
        }
    }

    private fun markAllVariablesAsEquals() {
        for (state in sfcDiff.states.values) {
            allVariables.forEach { v ->
                state.abstractVariable[v] = TaintEq.EQUAL
            }
        }
    }
}

private fun SMVExpr?.getVariables(): Set<String> {
    class SmvFindNameVisitor : SMVAstDefaultVisitor<Unit>() {
        val variables = TreeSet<String>()
        override fun visit(v: SVariable) {
            variables.add(v.name)
        }
    }

    val a = SmvFindNameVisitor()
    this?.accept(a)
    return a.variables
}

class ConstructDifferenceSfc(val leftPou: FunctionBlockDeclaration, val rightPou: FunctionBlockDeclaration)
    : Callable<DifferenceSfc> {
    val diffSfc = DifferenceSfc()
    val leftNetwork = leftPou.sfcBody?.networks!![0]
    val rightNetwork = rightPou.sfcBody?.networks!![0]

    val rightActions = HashMap<String, SymbolicState>()
    val leftActions = HashMap<String, SymbolicState>()

    override fun call(): DifferenceSfc {
        prepareActions(leftActions, leftPou)
        prepareActions(rightActions, rightPou)

        leftNetwork.steps.forEach {
            val diffStep = diffSfc.getState(it.name)
            translateAction(diffStep.leftAssignments, it.events, leftActions)
            translateTransitions(diffStep.leftIncomingTransitions, it.incoming, leftEvaluator)
        }

        rightNetwork.steps.forEach {
            val diffStep = diffSfc.getState(it.name)
            translateAction(diffStep.rightAssignments, it.events, rightActions)
            translateTransitions(diffStep.rightIncomingTransitions, it.incoming, rightEvaluator)
        }

        return diffSfc
    }

    private fun prepareActions(actions: HashMap<String, SymbolicState>,
                               pou: FunctionBlockDeclaration) {
        pou.actions.forEach { act ->
            actions[act.name] = executeAction(pou, act.stBody!!)
        }
    }

    private fun executeAction(pou: FunctionBlockDeclaration,
                              body: StatementList): SymbolicState {
        val program = ProgramDeclaration(scope = pou.scope.copy(), stBody = body)
        val se = SymbolicExecutioner(pou.scope.parent)
        program.accept(se)
        //remove to many assignments
        val state = se.peek().filter { (k, v) -> k != v }
        return SymbolicState(state)
    }

    fun evaluator(scope: Scope): SymbolicExecutioner {
        val se = SymbolicExecutioner()
        se.push(SymbolicState())
        for (vd in scope) {
            val s = se.lift(vd)
            se.peek()[s] = s
        }
        return se
    }

    val leftEvaluator = evaluator(leftPou.scope)
    val rightEvaluator = evaluator(rightPou.scope)

    private fun translateTransitions(incoming: MutableMap<DifferenceState, SMVExpr>,
                                     inc: MutableList<SFCTransition>,
                                     eval: SymbolicExecutioner) {
        inc.forEach { trans ->
            val from = trans.from.first()
            val to = trans.to.first()
            val guard = trans.guard
            val expr = guard.accept(eval)!!

            val sfrom = diffSfc.getState(from.name)
            val sto = diffSfc.getState(to.name)
            incoming[sfrom] = expr
        }

    }

    private fun translateAction(assignments: MutableMap<String, SMVExpr>,
                                events: Collection<SFCStep.AssociatedAction>,
                                actions: Map<String, SymbolicState>) {
        for (a in events) {
            actions[a.actionName]?.let { state ->
                state.forEach { a, v -> assignments[a.name] = v }
            }
        }
    }
}

data class DifferenceState(val name: String) {
    val leftAssignments: MutableMap<String, SMVExpr> = HashMap()
    val rightAssignments: MutableMap<String, SMVExpr> = HashMap()
    val abstractVariable: MutableMap<String, TaintEq> = HashMap()
    val leftIncomingTransitions: MutableMap<DifferenceState, SMVExpr> = HashMap()
    val rightIncomingTransitions: MutableMap<DifferenceState, SMVExpr> = HashMap()
}

class DifferenceSfc {
    val states: MutableMap<String, DifferenceState> = HashMap()
    fun getState(x: String) =
            states.computeIfAbsent(x) { DifferenceState(it) }

    fun toDot(stream: PrintWriter): Unit {
        stream.write("digraph G {\nnode[shape=none]\n")
        states.values.forEach {
            val variables = TreeSet(it.leftAssignments.keys + it.rightAssignments.keys)
            val htmlLabel = """<tr><td colspan="4">${it.name}</td></tr>""" +
                    variables.joinToString("\n") { v ->
                        val la = it.leftAssignments[v]?.repr().htmlEscape()
                        val ra = it.rightAssignments[v]?.repr().htmlEscape()
                        val taint = it.abstractVariable[v]?.toString()
                        "<tr><td>$v</td><td>${la}</td><td>${ra}</td><td>$taint</td></tr>"
                    }
            stream.write("${it.name} [label=<<table>$htmlLabel</table>> ]\n")
        }
        states.values.forEach { to ->
            val fromNodes = to.leftIncomingTransitions.keys + to.rightIncomingTransitions.keys
            fromNodes.forEach { from ->
                val left = to.leftIncomingTransitions[from]?.repr()
                val right = to.rightIncomingTransitions[from]?.repr()
                stream.write("${from.name} -> ${to.name} [label=\"${left} // ${right}\"]\n")
            }
        }
        stream.write("}\n")
        stream.flush()
    }
}

private fun String?.htmlEscape(): String? =
        this?.let {
            it.replace("&", "&amp;").replace("<", "&gt;").replace(">", "&lt;")
        }