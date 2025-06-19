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
package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.smv.ExpressionReplacerRecur
import edu.kit.iti.formal.smv.SMVAstVisitor
import edu.kit.iti.formal.smv.ast.SMVAst
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*
import kotlin.collections.HashMap
import kotlin.collections.component1
import kotlin.collections.component2
import kotlin.collections.set

const val ASSIGN_SEPARATOR: String = "\$"

interface SymbolicVariable {
    val variable: SVariable
    val value: SMVExpr
    fun push(value: SMVExpr, postfix: String)
    fun clone(): SymbolicVariable
}

/**
 * A symbolic variable represents a variable in the program.
 * Additional to its current value we remind every assignment to this variable.
 */
data class SymbolicVariableTracing(override val variable: SVariable) : SymbolicVariable {
    val values = TreeMap<SVariable, SMVExpr>()
    var current = variable

    override val value: SMVExpr
        get() = current

    override fun push(value: SMVExpr, postfix: String) {
        current = SVariable(variable.name + postfix, variable.dataType!!)
        values[current] = value
    }

    override fun clone(): SymbolicVariable {
        val sv = SymbolicVariableTracing(variable)
        sv.current = current
        sv.values.putAll(values)
        return sv
    }
}

data class SymbolicVariableSimple(override val variable: SVariable, override var value: SMVExpr = variable) : SymbolicVariable {
    override fun push(value: SMVExpr, postfix: String) {
        this.value = value
    }

    override fun clone(): SymbolicVariable = copy()
}

/**
 * Represents a symbolic state: a list of variable to expressions.
 *
 * The clou is that the we also allow a side-definitions.
 *
 * Every assignment is done as a side-definition.
 *
 */
data class SymbolicState(
    val variables: HashMap<SVariable, SymbolicVariable> = HashMap(),
    val useDefinitions: Boolean = true,
) : MutableMap<SVariable, SMVExpr> {

    val auxiliaryDefinitions: HashMap<SVariable, SMVExpr> = HashMap()

    constructor(m: SymbolicState) : this(useDefinitions = m.useDefinitions) {
        m.variables.forEach { (v, u) -> variables[v] = u.clone() }
        auxiliaryDefinitions.putAll(m.auxiliaryDefinitions)
    }

    operator fun get(x: String) = this[getKey(x)]
    fun getKey(x: String) = keys.find { it.name.equals(x, true) }

    override val size: Int
        get() = variables.size

    fun getCurrentValues(): Sequence<SMVExpr> = variables.values.asSequence().map { it.value }

    override fun containsKey(key: SVariable): Boolean = key in variables
    override fun containsValue(value: SMVExpr): Boolean = getCurrentValues().any { it == value }

    override fun get(key: SVariable): SMVExpr? = variables[key]?.value

    override fun isEmpty(): Boolean = variables.isEmpty()

    override val entries: MutableSet<MutableMap.MutableEntry<SVariable, SMVExpr>>
        get() = variables.entries.map { (a, b) ->
            object : MutableMap.MutableEntry<SVariable, SMVExpr> {
                override val key: SVariable
                    get() = a
                override val value: SMVExpr
                    get() = b.value

                override fun setValue(newValue: SMVExpr): SMVExpr = value
            }
        }.toMutableSet()

    override val keys: MutableSet<SVariable>
        get() = variables.keys

    override val values: MutableCollection<SMVExpr>
        get() = getCurrentValues().toMutableList()

    override fun clear() = variables.clear()

    override fun put(key: SVariable, value: SMVExpr): SMVExpr? =
        throw IllegalArgumentException("Use assign(...) instead")

    fun assign(key: SVariable, assignCounter: Int, v: SMVExpr) {
        val s = ensureVariable(key)
        val postfix = String.format("%s%05d", ASSIGN_SEPARATOR, assignCounter)
        s.push(v, postfix)
    }

    fun ensureVariable(key: SVariable) = variables.computeIfAbsent(key) {
        if (useDefinitions) {
            SymbolicVariableTracing(key)
        } else {
            SymbolicVariableSimple(key)
        }
    }

    override fun putAll(from: Map<out SVariable, SMVExpr>) {
        from.forEach { (a, b) -> put(a, b) }
    }

    override fun remove(key: SVariable): SMVExpr? {
        val ss = variables.remove(key)
        return ss?.value
    }

    override fun toString(): String {
        val sb = StringBuffer()
        entries.joinTo(sb, prefix = "{", postfix = "}") { (k, v) ->
            "${k.name}=${v.repr()}"
        }
        return sb.toString()
    }

    /**
     * Get an representation of this state without any use of definitions.
     */
    fun unfolded(): Map<SVariable, SMVExpr> {
        var m = variables.map { (a, b) -> a to b.value }.toMap()
        val defs = getAllDefinitions()
        val r = ExpressionReplacerRecur(defs)
        while (true) {
            r.changed = false
            val updated = m.map { (t, u) ->
                t to u.accept(r as SMVAstVisitor<SMVAst>) as SMVExpr
            }.toMap()
            m = updated
            if (!r.changed) break
        }
        return m
    }

    fun getAllDefinitions(): Map<SVariable, SMVExpr> {
        val defs: HashMap<SVariable, SMVExpr> = HashMap()
        defs.putAll(auxiliaryDefinitions)

        for ((_, b) in variables) {
            if (b is SymbolicVariableTracing) {
                defs.putAll(b.values)
            }
        }

        return defs
    }
}