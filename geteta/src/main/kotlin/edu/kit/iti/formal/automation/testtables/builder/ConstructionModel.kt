package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.testtables.algorithms.StateReachability
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ParseContext
import edu.kit.iti.formal.automation.testtables.model.State
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
class ConstructionModel(val superEnumType: SMVType,
                        val testTable: GeneralizedTestTable,
                        val clocks: MutableMap<State, SVariable>) {
    val variableContext: ParseContext = testTable.generateSmvExpression()
    val tableModule = SMVModule("...")
    val helperModules = LinkedList<SMVModule>()
    val ERROR_STATE_IDENTIFIER = "_\$ERROR"
    val SENTINEL_STATE_IDENTIFIER = "_\$SENTINEL"
    //val errorState = SVariable(ERROR_STATE_IDENTIFIER, SMVType.BOOLEAN)
    val sentinelState = State(SENTINEL_STATE_IDENTIFIER)
    val sentinelVariable = sentinelState.automataStates[0].smvVariable
    val errorState = State(ERROR_STATE_IDENTIFIER)
    val errorVariable = errorState.automataStates[0].smvVariable
    val reachable: StateReachability = StateReachability(this)
}
