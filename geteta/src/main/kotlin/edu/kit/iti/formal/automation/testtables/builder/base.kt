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
package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.testtables.algorithms.StateReachability
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ParseContext
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.SpecialState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.smv.ModuleType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.conjunction
import java.util.*
import kotlin.collections.HashMap

interface Transformer<T : Any> {
    fun transform(model: T)
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
class SMVConstructionModel(val superEnumType: SMVType, state: AutomataTransformerState) {
    lateinit var variableContext: ParseContext
    val testTable: GeneralizedTestTable = state.testTable
    val automaton = state.automaton

    val tableModule = SMVModule("...")
    val helperModules: MutableList<SMVModule> = LinkedList()

    val sentinelState = automaton.stateSentinel
    val stateError = SVariable(automaton.stateError.name, SMVTypes.BOOLEAN)
    var stateSentinel = SVariable(automaton.stateSentinel.name, SMVTypes.BOOLEAN)
    var ttType: ModuleType? = null
    val rowStates: List<RowState>
        get() = automaton.rowStates.values.flatMap { it }

    val definitions = HashMap<String, SMVExpr>()

    fun define(v: SVariable, expr: SMVExpr) {
        if (v.name in definitions) {
            require(expr == definitions[v.name]) {
                "Collision of definitions for variable ${v.repr()}. " +
                    "Previous assigned to ${definitions[v.name]?.repr()}, newly assigned to ${expr.repr()}."
            }
        } else {
            definitions[v.name] = expr
            tableModule.definitions.add(SAssignment(v, expr))
        }
    }

    fun define(variable: SVariable, expr: MutableMap<String, SMVExpr>) {
        val names = expr.entries.map { (k, v) ->
            SVariable(variable.name + "_" + k, SMVTypes.BOOLEAN).also {
                define(it, v)
            }
        }
        define(variable, names.conjunction(default = SLiteral.TRUE))
    }

    fun getStateVariable(ss: RowState) = SVariable(ss.name, SMVTypes.BOOLEAN)

    fun getMiss(ss: RowState): SVariable = SVariable(ss.miss, SMVTypes.BOOLEAN)

    fun getAccept(ss: RowState): SVariable = SVariable(ss.fwd, SMVTypes.BOOLEAN)

    fun getAcceptProgress(ss: RowState): SVariable = SVariable(ss.fwdprogress, SMVTypes.BOOLEAN)

    fun getFail(ss: RowState): SVariable = SVariable(ss.fail, SMVTypes.BOOLEAN)

    fun getVariable(to: AutomatonState): SVariable = when (to) {
        is SpecialState -> if (to == automaton.stateSentinel) stateSentinel else stateError
        is RowState -> getStateVariable(to)
    }
}

typealias SmvConstructionTransformer = Transformer<SMVConstructionModel>

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
abstract class AbstractTransformer<T : Any> : Transformer<T> {
    lateinit var model: T
    override fun transform(model: T) {
        this.model = model
        transform()
    }

    abstract fun transform()
}

/***********************************************************************************/

class AutomataTransformerState(
    val testTable: GeneralizedTestTable,
    val automaton: TestTableAutomaton,
) {
    lateinit var flatRegion: List<TableRow>
    lateinit var stateReachability: StateReachability
}
typealias AutomatonConstructionTransformer = Transformer<AutomataTransformerState>
