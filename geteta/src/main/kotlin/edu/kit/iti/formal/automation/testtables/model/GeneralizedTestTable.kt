/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.model


import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.st.ArrayLookupList
import edu.kit.iti.formal.automation.st.Cloneable
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.SetLookupList
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.testtables.algorithms.StateReachability
import edu.kit.iti.formal.automation.testtables.io.IOFacade
import edu.kit.iti.formal.automation.testtables.model.options.PropertyInitializer
import edu.kit.iti.formal.automation.testtables.model.options.TableOptions
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

sealed class Variable : Identifiable, Cloneable {
    abstract override var name: String
    abstract var dataType: AnyDt
}

enum class IoVariableType {
    INPUT, OUTPUT, STATE_INPUT, STATE_OUTPUT
}

data class IoVariable(
        override var name: String,
        override var dataType: AnyDt,
        var io: IoVariableType) : Variable() {
    override fun clone() = copy()
    var realName: String = name


    val isInput
        get() = io == IoVariableType.INPUT || io == IoVariableType.STATE_INPUT

    val isOutput
        get() = !isInput

}

data class ConstraintVariable(
        override var name: String,
        override var dataType: AnyDt,
        var constraint: SMVExpr = SLiteral.TRUE)
    : Variable() {
    override fun clone() = copy()
}

/**
 * @author Alexander Weigl
 * @version 2
 */
class GeneralizedTestTable {
    val ioVariables = ArrayLookupList<IoVariable>()
    val constraintVariables = SetLookupList<ConstraintVariable>()
    private val variableMap = HashMap<String, SVariable>()
    private val properties = Properties(
            System.getProperties())
    val functions = SetLookupList<FunctionDeclaration>()
    val references = HashMap<SVariable, Int>()
    var region: Region? = null

    val options: TableOptions by lazy {
        val o = TableOptions()
        PropertyInitializer.initialize(o, properties)
        o
    }
    var name: String? = null

    fun clearReachability() {
        for (s in this.region!!.flat()) {
            s.outgoing.clear()
            s.incoming.clear()
            s.automataStates.clear()

            for (a in s.automataStates) {
                a.outgoing.clear()
                a.incoming.clear()
            }
        }
    }

    fun getSMVVariable(text: IoVariable): SVariable = getSMVVariable(text.name)
    fun getSMVVariable(text: String): SVariable {
        return variableMap.computeIfAbsent(text) { k ->
            IOFacade.asSMVVariable(getVariable(k))
        }
        //return variableMap[text] ?: error("Looked up non-existing variable.")
    }

    fun isVariable(text: String) = text in ioVariables || text in constraintVariables


    private fun getVariable(text: String): Variable {
        val a = ioVariables[text]
        val b = constraintVariables[text]

        if (a != null && b != null)
            throw IllegalStateException(
                    "constraint and io variable have the same name.")

        return a ?: b ?: error("Could not found a variable with $text in signature.")
    }

    fun add(v: IoVariable) {
        ioVariables += v
    }

    fun add(v: ConstraintVariable) {
        constraintVariables += v
    }

    fun addOption(key: String, value: String) {
        properties[key] = value
        //options = null // reset options
    }

    fun getIoVariables(i: Int): IoVariable = ioVariables[i]

    fun getReferences(): Map<SVariable, Int> {
        return references
    }

    fun getReference(columnVariable: SVariable, i: Int): SMVExpr {
        if (i == 0) {
            return columnVariable
        } else {
            val ref = SReference(i, columnVariable)
            val max = Math.max((references as java.util.Map<SVariable, Int>).getOrDefault(columnVariable, i), i)
            references[columnVariable] = max
            return ref.asVariable()
        }
    }
}
