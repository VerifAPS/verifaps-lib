package edu.kit.iti.formal.automation.testtables.model

import edu.kit.iti.formal.smv.ast.SMVExpr

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
data class Transition(
        val from: String,
        val to: String,
        var guard: SMVExpr
)

class Automata {
    val initialStates: MutableSet<String> = HashSet()
    val states: MutableSet<String> = HashSet()
    val transitions: MutableList<Transition> = ArrayList()

    fun initial(state: String) {
        initialStates.add(state)
    }

    fun add(state: String) {
        states.add(state)
    }

    fun remove(state: String) {
        states.remove(state)
    }

    fun addTransition(from: String, to: String, guard: SMVExpr) {
        val t = getTransition(from, to)
        if (t != null) {
            t.guard = t.guard.or(guard)
        } else {
            transitions.add(Transition(from, to, guard))
        }
    }

    fun getTransition(from: String, to: String): Transition? = transitions.firstOrNull { it.from == from && it.to == to }

    fun clear() {
        transitions.clear()
        states.clear()
        initialStates.clear()
    }
}