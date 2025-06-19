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
package edu.kit.iti.formal.automation.absint

import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.automation.st.ast.SFCStep
import edu.kit.iti.formal.automation.st.ast.SFCTransition
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.smv.SMVAstScanner
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.info
import java.awt.Color
import java.io.PrintWriter
import java.util.*
import java.util.concurrent.Callable
import kotlin.collections.HashMap
import kotlin.math.roundToInt

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.11.18)
 */
class AbstractInterpretationSfc(val sfcDiff: DifferenceSfc, val leftScope: Scope, val rightScope: Scope) : Runnable {
    val lattice = TaintEqLattice()
    val allVariables =
        TreeSet(
            leftScope.variables.map { it.name } +
                rightScope.variables.map { it.name },
        )

    override fun run() {
        var change: Boolean
        info("Mark all variables as equals")
        var iter = 1
        markAllVariablesAsEquals()
        do {
            info("$iter Iteration")
            val update = sfcDiff.states.values.map {
                val c = updateState(it)
                if (c) {
                    info("Next iteration will happen: ${it.name} changed!")
                }
                c
            }
            change = update.any { it }
            info("Change is $change.")
            iter++
        } while (change)

        updateGuards()
    }

    private fun updateGuards() {
        sfcDiff.states.values.forEach { to ->
            val leftT = to.leftIncomingTransitions
            val rightT = to.rightIncomingTransitions
            val incomingStates = leftT.keys + rightT.keys
            incomingStates.forEach { from ->
                val leftGuard = leftT[from]
                val rightGuard = rightT[from]
                to.abstractGuard[from] = updateAssignment(from.abstractVariable, leftGuard, rightGuard)
            }
        }
    }

    private fun updateState(it: DifferenceState): Boolean {
        val oldState = it.abstractVariable.toMap()
        val incomingNode = it.leftIncomingTransitions.keys + it.rightIncomingTransitions.keys

        val incomingTaint =
            if (incomingNode.isEmpty()) {
                allVariables.map { it to TaintEq.EQUAL }.toMap()
            } else {
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
            }
        val variables = (it.rightAssignments.keys + it.leftAssignments.keys)
        variables.forEach { v ->
            val leftExpr = it.leftAssignments[v]
            val rightExpr = it.rightAssignments[v]
            val new = updateAssignment(incomingTaint, leftExpr, rightExpr)
            val old = it.abstractVariable[v]!!
            it.abstractVariable[v] = new
            if (new != old) {
                info("Value changed in ${it.name} for $v.")
            }
        }

        return it.abstractVariable.any { (v, eq) -> eq != oldState[v] }
    }

    private fun updateAssignment(
        incomingTaint: Map<String, TaintEq>,
        leftExpr: SMVExpr?,
        rightExpr: SMVExpr?,
    ): TaintEq {
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
    class SmvFindNameVisitor : SMVAstScanner() {
        val variables = TreeSet<String>()
        override fun visit(v: SVariable) {
            variables.add(v.name)
        }
    }

    val a = SmvFindNameVisitor()
    this?.accept(a)
    return a.variables
}

class ConstructDifferenceSfc(
    val leftPou: FunctionBlockDeclaration,
    val rightPou: FunctionBlockDeclaration,
    val prefill: Boolean,
) : Callable<DifferenceSfc> {
    val diffSfc = DifferenceSfc()
    val leftNetwork = leftPou.sfcBody?.networks!![0]
    val rightNetwork = rightPou.sfcBody?.networks!![0]

    val rightActions = HashMap<String, SymbolicState>()
    val leftActions = HashMap<String, SymbolicState>()

    override fun call(): DifferenceSfc {
        prepareActions(leftActions, leftPou)
        prepareActions(rightActions, rightPou)

        if (prefill) {
            val leftEqualState = executeAction(leftPou, StatementList())
            val rightEqualState = executeAction(leftPou, StatementList())
            val stateNames = (leftNetwork.steps + rightNetwork.steps).map { it.name }
            // populate all steps with id assignments.
            stateNames.forEach {
                val diffStep = diffSfc.getState(it)
                leftEqualState.forEach { t, u -> diffStep.leftAssignments[t.name] = u }
                rightEqualState.forEach { t, u -> diffStep.rightAssignments[t.name] = u }
            }
        }

        leftNetwork.steps.forEach {
            val diffStep = diffSfc.getState(it.name)
            translateAction(diffStep.leftAssignments, it.events, leftActions, leftPou)
            translateTransitions(diffStep.leftIncomingTransitions, it.incoming, leftEvaluator)
        }

        rightNetwork.steps.forEach {
            val diffStep = diffSfc.getState(it.name)
            translateAction(diffStep.rightAssignments, it.events, rightActions, rightPou)
            translateTransitions(diffStep.rightIncomingTransitions, it.incoming, rightEvaluator)
        }

        return diffSfc
    }

    private fun prepareActions(actions: HashMap<String, SymbolicState>, pou: FunctionBlockDeclaration) {
        pou.actions.forEach { act ->
            actions[act.name] = executeAction(pou, act.stBody!!)
        }
    }

    private fun executeAction(pou: FunctionBlockDeclaration, body: StatementList): SymbolicState {
        val program = ProgramDeclaration(scope = pou.scope.copy(), stBody = body)
        val se = SymbolicExecutioner(pou.scope.parent!!)
        program.accept(se)
        // remove to many assignments
        val state = se.peek() // .filter { (k, v) -> k != v }
        return SymbolicState(state)
    }

    fun evaluator(scope: Scope): SymbolicExecutioner {
        val se = SymbolicExecutioner()
        se.push(SymbolicState())
        for (vd in scope) {
            val s = se.lift(vd)
            se.assign(vd, s)
        }
        return se
    }

    val leftEvaluator = evaluator(leftPou.scope)
    val rightEvaluator = evaluator(rightPou.scope)

    private fun translateTransitions(
        incoming: MutableMap<DifferenceState, SMVExpr>,
        inc: MutableList<SFCTransition>,
        eval: SymbolicExecutioner,
    ) {
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

    private fun translateAction(
        assignments: MutableMap<String, SMVExpr>,
        events: Collection<SFCStep.AssociatedAction>,
        actions: Map<String, SymbolicState>,
        pou: FunctionBlockDeclaration,
    ) {
        if (events.isEmpty()) { // Assume empty action block
            val state = executeAction(pou, StatementList())
            state.forEach { a, v -> assignments[a.name] = v }
        } else {
            for (a in events) {
                actions[a.actionName]?.let { state ->
                    state.forEach { a, v -> assignments[a.name] = v }
                }
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
    val abstractGuard: MutableMap<DifferenceState, TaintEq> = HashMap()
}

class DifferenceSfc {
    val states: MutableMap<String, DifferenceState> = HashMap()
    fun getState(x: String) = states.computeIfAbsent(x) { DifferenceState(it) }

    fun toDot(
        stream: PrintWriter,
        showExprs: Boolean = false,
        showEqualVars: Boolean = false,
        showNoVariables: Boolean = false,
    ) {
        stream.write("digraph G {\nnode[shape=none]\n")
        states.values.forEach {
            val variables = it.abstractVariable.keys
            val numEqualVars =
                it.abstractVariable.values.filter { it == TaintEq.EQUAL }
                    .size

            val color = interpolate(Color.RED, Color.GREEN, numEqualVars.toDouble() / variables.size)
            val variablesToBeShown =
                when {
                    showNoVariables -> setOf()
                    showEqualVars -> variables
                    else -> variables.filter { v -> it.abstractVariable[v] == TaintEq.NOT_EQUAL }
                }

            val htmlLabel = """<tr><td colspan="4"><B><U>${it.name}</U></B></td></tr>""" +
                variablesToBeShown.joinToString("\n") { v ->
                    val la =
                        if (showExprs) it.leftAssignments[v]?.repr().htmlEscape() else ""
                    val ra =
                        if (showExprs) it.rightAssignments[v]?.repr().htmlEscape() else ""
                    val taint = it.abstractVariable[v]
                    val c = if (taint == TaintEq.EQUAL) "green" else "red"
                    "<tr><td><B>$v</B></td><td>$la</td><td>$ra</td>" +
                        "<td><font color=\"$c\">$taint</font></td></tr>"
                }
            stream.write("${it.name} [color=\"$color\",label=<<table CELLBORDER=\"0\">$htmlLabel</table>> ]\n")
        }
        states.values.forEach { to ->
            val fromNodes = to.leftIncomingTransitions.keys + to.rightIncomingTransitions.keys
            fromNodes.forEach { from ->
                val left = to.leftIncomingTransitions[from]?.repr()
                val right = to.rightIncomingTransitions[from]?.repr()
                val taint = to.abstractGuard[from]
                val color = if (taint == TaintEq.EQUAL) "green" else "red"
                stream.write("${from.name} -> ${to.name} [color=$color,label=\"$taint ($left // $right)\"]\n")
            }
        }
        stream.write("}\n")
        stream.flush()
    }

    private fun interpolate(red: Color, green: Color, factor: Double): String {
        fun lr(a: Int, b: Int) = (a * (1 - factor) + b * factor).roundToInt()

        val r = lr(red.red, green.red)
        val g = lr(red.green, green.green)
        val b = lr(red.blue, green.blue)

        return String.format("#%02X%02X%02X", r, g, b)
    }
}

private fun String?.htmlEscape(): String? = this?.let {
    it.replace("&", "&amp;").replace("<", "&gt;").replace(">", "&lt;")
}