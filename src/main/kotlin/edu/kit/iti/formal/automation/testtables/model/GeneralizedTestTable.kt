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


import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.TopLevelElement
import edu.kit.iti.formal.automation.testtables.StateReachability
import edu.kit.iti.formal.automation.testtables.io.IOFacade
import edu.kit.iti.formal.automation.testtables.model.options.PropertyInitializer
import edu.kit.iti.formal.automation.testtables.model.options.TableOptions
import edu.kit.iti.formal.automation.testtables.schema.ConstraintVariable
import edu.kit.iti.formal.automation.testtables.schema.IoVariable
import edu.kit.iti.formal.automation.testtables.schema.Variable
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable

import java.util.*

/**
 * @author Alexander Weigl
 * @version 2
 */
class GeneralizedTestTable {
    private val ioVariables = LinkedHashMap<String, IoVariable>()
    private val constraintVariables = HashMap<String, ConstraintVariable>()
    private val variableMap = HashMap<String, SVariable>()
    private val properties = Properties(
            System.getProperties())
    private val functions = HashMap<String, FunctionDeclaration>()
    private val references = HashMap<SVariable, Int>()
    var region: Region? = null
    var options: TableOptions? = null
        get() {
            if (field == null) {
                field = TableOptions()
                PropertyInitializer.initialize(field, properties)
            }
            return field
        }
    var name: String? = null

    val constraintVariable: Map<String, ConstraintVariable>
        get() = constraintVariables

    fun calculateReachability() {
        for (s in this.region!!.flat()) {
            s.outgoing.clear()
            s.incoming.clear()
            s.automataStates.clear()

            for (a in s.automataStates) {
                a.outgoing.clear()
                a.incoming.clear()
            }
        }
        StateReachability(this)
    }

    fun getIoVariables(): Map<String, IoVariable> {
        return ioVariables
    }

    fun getSMVVariable(text: String): SVariable {
        variableMap.computeIfAbsent(text) { k ->
            IOFacade.asSMVVariable(getVariable(k))
        }
        return variableMap[text]
    }

    private fun getVariable(text: String): Variable? {
        val a = ioVariables[text]
        val b = constraintVariables[text]

        if (a != null && b != null)
            throw IllegalStateException(
                    "constraint and io variable have the same name.")

        return a ?: b
    }

    fun add(v: IoVariable) {
        ioVariables[v.name] = v
    }

    fun add(v: ConstraintVariable) {
        constraintVariables[v.name] = v
    }

    fun addOption(key: String, value: String) {
        properties[key] = value
        options = null // reset options
    }

    fun addFunctions(file: List<TopLevelElement<*>>) {
        for (e in file) {
            functions[e.identifier] = e as FunctionDeclaration
        }
    }

    fun getIoVariables(i: Int): IoVariable? {
        var k = 0
        for (v in ioVariables.values) {
            if (k++ == i)
                return v
        }
        return null
    }

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
