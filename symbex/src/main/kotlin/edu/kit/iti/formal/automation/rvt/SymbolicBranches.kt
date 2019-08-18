package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.smv.ast.SCaseExpression
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable

/**
 * Created by weigl on 27.11.16.
 */
class SymbolicBranches {
    private val variables: HashMap<SVariable, SCaseExpression> = HashMap()
    private val defines = HashMap<SVariable, HashMap<SVariable, SMVExpr>>()

    fun addBranch(condition: SMVExpr, state: SymbolicState) {
        for ((key, value) in state.map) {
            getVariable(key).add(condition, if (state.useDefinitions) value.current else value.value!!)
            getDefines(key).putAll(value.values)
        }
    }

    fun getVariable(key: SVariable): SCaseExpression = variables.computeIfAbsent(key) { SCaseExpression() }
    fun getDefines(key: SVariable): HashMap<SVariable, SMVExpr> = defines.computeIfAbsent(key) { HashMap() }

    /**
     *
     */
    fun asCompressed(assignCounter: Int): SymbolicState {
        val sb = SymbolicState()
        variables.forEach { (t, u) ->
            val sv = SymbolicVariable(t)
            sv.push(u.compress(), "_${assignCounter}")
            defines[t]?.let { sv.values.putAll(it) }
            sb.map[t] = sv
        }
        return sb
    }
}
