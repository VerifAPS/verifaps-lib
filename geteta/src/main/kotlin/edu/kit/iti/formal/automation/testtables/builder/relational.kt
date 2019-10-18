package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.testtables.model.ColumnCategory
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.automation.testtables.rtt.VARIABLE_PAUSE
import edu.kit.iti.formal.smv.SMVTypes

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.08.18)
 */
object PauseAdder : AbstractTransformer<SMVConstructionModel>() {
    override fun transform() {
        model.testTable.programRuns.forEachIndexed { i, it ->
            model.testTable.programVariables +=
                    ProgramVariable(VARIABLE_PAUSE, AnyBit.BOOL, SMVTypes.BOOLEAN,
                            ColumnCategory.ASSUME, programRun = i)
        }
    }
}
