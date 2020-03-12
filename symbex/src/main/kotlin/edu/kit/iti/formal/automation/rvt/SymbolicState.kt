package edu.kit.iti.formal.automation.rvt

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.smv.SMVAstMutableVisitor
import edu.kit.iti.formal.smv.SMVAstVisitor
import edu.kit.iti.formal.smv.ast.*
import java.util.*
import kotlin.collections.HashMap
import kotlin.collections.HashSet

const val ASSIGN_SEPARATOR: String = "\$"


data class SymbolicVariable(val variable: SVariable) {
    val values = TreeMap<SVariable, SMVExpr>()
    var current = variable

    val value
        get() = values[current]

    fun push(value: SMVExpr, postfix: String) {
        current = SVariable(variable.name + postfix, variable.dataType!!)
        values[current] = value
    }

    fun clone(): SymbolicVariable {
        val sv = SymbolicVariable(variable)
        sv.current = current
        sv.values.putAll(values)
        return sv
    }
}

/**
 * Created by weigl on 27.11.16.
 */
data class SymbolicState(val definitions: HashMap<SVariable, SymbolicVariable> = HashMap())
    : MutableMap<SVariable, SMVExpr> {
    val auxiliaryDefinitions: HashMap<SVariable, SMVExpr> = HashMap()

    constructor(m: SymbolicState) : this() {
        m.definitions.forEach { (v, u) -> definitions[v] = u.clone() }
    }

    operator fun get(x: String) = this[getKey(x)]
    fun getKey(x: String) = keys.find { it.name.equals(x, true) }

    var useDefinitions: Boolean = true

    override val size: Int
        get() = definitions.size

    fun getCurrentValues(): Sequence<SMVExpr> =
            definitions.values.asSequence().map { it.value!! }

    override fun containsKey(key: SVariable): Boolean = key in definitions
    override fun containsValue(value: SMVExpr): Boolean =
            getCurrentValues().any { it == value }

    override fun get(key: SVariable): SMVExpr? =
            definitions[key]?.let {
                if (useDefinitions) it.current
                else it.value
            }


    override fun isEmpty(): Boolean = definitions.isEmpty()

    override val entries: MutableSet<MutableMap.MutableEntry<SVariable, SMVExpr>>
        get() = definitions.entries.map { (a, b) ->
            object : MutableMap.MutableEntry<SVariable, SMVExpr> {
                override val key: SVariable
                    get() = a
                override val value: SMVExpr
                    get() = if (useDefinitions) b.current else b.value!!

                override fun setValue(newValue: SMVExpr): SMVExpr {
                    return value
                }
            }
        }.toMutableSet()

    override val keys: MutableSet<SVariable>
        get() = definitions.keys

    override val values: MutableCollection<SMVExpr>
        get() = getCurrentValues().toMutableList()

    override fun clear() = definitions.clear()

    override fun put(key: SVariable, value: SMVExpr): SMVExpr? = throw IllegalArgumentException("Use assign(...) instead")

    fun assign(key: SVariable, assignCounter: Int, v: SMVExpr) {
        val s = definitions[key] ?: SymbolicVariable(key).also { definitions[key] = it }
        val postfix = String.format("%s%05d", ASSIGN_SEPARATOR, assignCounter)
        s.push(v, postfix)
    }

    override fun putAll(from: Map<out SVariable, SMVExpr>) {
        from.forEach { (a, b) -> put(a, b) }
    }

    override fun remove(key: SVariable): SMVExpr? {
        val ss = definitions.remove(key)
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
        var m = definitions.map { (a, b) -> a to b.value!! }.toMap()
        val defs = getAllDefinitions()
        val r = ExpressionReplacer(defs)
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

    fun getAllDefinitions() =
            definitions.flatMap { (_, b) -> b.values.entries }
                    .map { (a, b) -> a to b }
                    .toMap() + auxiliaryDefinitions

    /*private val auxVariables = HashSet<SVariable>()
    fun markAsAuxiliary(key: SVariable) = auxVariables.add(key)
    fun isAuxiliary(key: SVariable) = key in auxVariables*/
}

class ExpressionReplacer(private val assignments: Map<out SMVExpr, SMVExpr>) : SMVAstMutableVisitor() {
    var changed = false
    override fun visit(v: SVariable): SMVExpr {
        val a = assignments[v]
        return if (a == null) super.visit(v) else {
            changed = true; a
        }
    }

    override fun visit(v: SBinaryExpression): SMVExpr {
        val a = assignments[v]
        return if (a == null) super.visit(v) else {
            changed = true; a
        }
    }

    override fun visit(v: SUnaryExpression): SMVExpr {
        val a = assignments[v]
        return if (a == null) super.visit(v) else {
            changed = true; a
        }
    }

    override fun visit(v: SLiteral): SMVExpr {
        val a = assignments[v]
        return if (a == null) super.visit(v) else {
            changed = true; a
        }
    }

    override fun visit(v: SFunction): SMVExpr {
        val a = assignments[v]
        return if (a == null) super.visit(v) else {
            changed = true; a
        }
    }

    override fun visit(v: SQuantified): SMVExpr {
        val a = assignments[v]
        return if (a == null) super.visit(v) else {
            changed = true; a
        }
    }
}
