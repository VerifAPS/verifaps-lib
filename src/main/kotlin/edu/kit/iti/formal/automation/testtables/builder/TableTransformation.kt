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
package edu.kit.iti.formal.automation.testtables.builder


import edu.kit.iti.formal.automation.testtables.StateReachability
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableModule
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SMVType
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.LinkedList
import java.util.function.Consumer

class TableTransformation(val testTable: GeneralizedTestTable, val superEnumType: SMVType) {
    val reachable: StateReachability
    private val transformers = LinkedList<Consumer<TableTransformation>>()
    val tableModule = TableModule()

    private val helper = LinkedList<SMVModule>()

    val helperModules: Collection<SMVModule>
        get() = helper

    init {
        reachable = StateReachability(testTable)
        init()
    }

    fun getSentinelState(): SVariable {
        return sentinelState
    }


    private fun init() {
        transformers.clear()
        transformers.add(NameSetterTransformer())
        transformers.add(ModuleParameterTransformer())
        transformers.add(StatesTransformer())
        transformers.add(ConstraintVariableTransformer())
        transformers.add(BackwardsReferencesTransformer())
        transformers.add(LTLSpecTransformer())

        when (testTable.options.mode) {
            Mode.CONFORMANCE -> transformers.add(ConformanceInvariantTransformer())
            Mode.CONCRETE_TABLE -> transformers.add(ConcreteTableInvariantTransformer())
            Mode.INPUT_SEQUENCE_EXISTS -> transformers.add(InputSequenceInvariantTransformer())
        }
    }

    fun transform(): SMVModule {
        transformers.forEach { a -> a.accept(this) }
        return tableModule
    }

    fun getErrorState(): SVariable {
        return errorState
    }

    companion object {
        val ERROR_STATE_IDENTIFIER = "_\$ERROR"
        private val SENTINEL_STATE_IDENTIFIER = "_\$SENTINEL"
        private val errorState = SVariable(ERROR_STATE_IDENTIFIER, SMVType.BOOLEAN)
        private val sentinelState = SVariable(SENTINEL_STATE_IDENTIFIER, SMVType.BOOLEAN)
    }
}
