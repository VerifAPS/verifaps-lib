package edu.kit.iti.formal.automation.testtables.builder


import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.testtables.model.ColumnCategory
import edu.kit.iti.formal.automation.testtables.model.ControlCommand
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.automation.testtables.model.chapterMarksForProgramRuns
import edu.kit.iti.formal.automation.testtables.rtt.VARIABLE_PAUSE
import edu.kit.iti.formal.automation.testtables.rtt.resetVariable
import edu.kit.iti.formal.automation.testtables.rtt.setVariable
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.util.fail

/**
 * Translate the [ControlCommand.Pause] into the assumption
 * @author Alexander Weigl
 * @version 1 (04.08.18)
 */
object PlayPauseToAssumption : AbstractTransformer<SMVConstructionModel>() {
    override fun transform() {
        // Add the pause variable into the table signature
        model.testTable.programRuns.forEachIndexed { i, _ ->
            model.testTable.programVariables +=
                    ProgramVariable(VARIABLE_PAUSE, AnyBit.BOOL, SMVTypes.BOOLEAN,
                            ColumnCategory.ASSUME, programRun = i)
        }

        model.testTable.region.flat().forEach {
            val pauseProgramRuns = it.pauseProgramRuns
            model.testTable.programRuns.forEachIndexed { i, _ ->
                val stutter = i in pauseProgramRuns
                it.inputExpr[VARIABLE_PAUSE] = if (stutter) SLiteral.TRUE else SLiteral.FALSE
            }
        }
    }
}

object BackwardToAssumption : AbstractTransformer<SMVConstructionModel>() {
    override fun transform() {
        val cmarks = model.testTable.chapterMarksForProgramRuns
        //add input variables set and reset to the table signature
        cmarks.forEach { (run, tableRows) ->
            tableRows.forEach { row ->
                model.testTable.programVariables +=
                        ProgramVariable(setVariable(row), AnyBit.BOOL, SMVTypes.BOOLEAN,
                                ColumnCategory.ASSUME, programRun = run)
                model.testTable.programVariables +=
                        ProgramVariable(resetVariable(row), AnyBit.BOOL, SMVTypes.BOOLEAN,
                                ColumnCategory.ASSUME, programRun = run)
            }
        }

        val rows = model.testTable.region.flat()
        //translate backward(n)
        for (tableRow in rows) {
            for ((run, targets) in cmarks) {
                for (target in targets) {
                    val isJumpTarget = tableRow.id == target
                    tableRow.inputExpr[setVariable(tableRow.id)] = //TODO how to distinguish from the other inputs? run is needed
                            if (isJumpTarget) SLiteral.TRUE else SLiteral.FALSE

                    if (tableRow.duration.isOneStep) {
                        fail("The table row ${tableRow.id} in table ${model.testTable.name} is addressed by a backward-jump, " +
                                "but does not have the required of duration [1,1]. Please split up the row manually. ")
                    }
                }
            }

            val backwardCommands =
                    tableRow.controlCommands.filterIsInstance<ControlCommand.Backward>()

            for ((run, targets) in cmarks) {
                for (target in targets) {
                    val resetActivated = null != backwardCommands.find {
                        it.affectedProgramRun == run && it.jumpToRow == target
                    }
                    tableRow.inputExpr[resetVariable(target)] = if (resetActivated) SLiteral.TRUE else SLiteral.FALSE
                }
            }
        }
    }
}