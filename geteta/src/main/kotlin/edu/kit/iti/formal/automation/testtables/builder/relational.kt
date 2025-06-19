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

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.testtables.model.ColumnCategory
import edu.kit.iti.formal.automation.testtables.model.ControlCommand
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.automation.testtables.model.chapterMarksForProgramRuns
import edu.kit.iti.formal.automation.testtables.rtt.pauseVariableP
import edu.kit.iti.formal.automation.testtables.rtt.resetVariableP
import edu.kit.iti.formal.automation.testtables.rtt.setVariableP
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.fail

/**
 * Translate the [ControlCommand.Pause] into the assumption
 * @author Alexander Weigl
 * @version 1 (04.08.18)
 */
object PlayPauseToAssumption : AbstractTransformer<SMVConstructionModel>() {
    override fun transform() {
        // Add the pause variable into the table signature
        val pauseVars = model.testTable.programRuns.mapIndexed { i, _ ->
            ProgramVariable(
                pauseVariableP(),
                AnyBit.BOOL,
                SMVTypes.BOOLEAN,
                ColumnCategory.ASSUME,
                programRun = i,
            )
        }
        model.testTable.programVariables.addAll(pauseVars)
        model.testTable.region.flat().forEach {
            pauseVars.forEachIndexed { i, run ->
                val stutter = i in it.pauseProgramRuns
                val variable = run.internalVariable(model.testTable.programRuns)
                it.inputExpr[variable.name] =
                    if (stutter) variable else variable.not()
            }
        }
    }
}

object BackwardToAssumption : AbstractTransformer<SMVConstructionModel>() {
    override fun transform() {
        val cmarks = model.testTable.chapterMarksForProgramRuns
        // add input variables set and reset to the table signature
        val setVariables = HashMap<Pair<Int, String>, SVariable>()
        val resetVariables = HashMap<Pair<Int, String>, SVariable>()

        cmarks.forEach { (run, tableRows) ->
            tableRows.forEach { row ->
                val set = ProgramVariable(
                    setVariableP(row),
                    AnyBit.BOOL,
                    SMVTypes.BOOLEAN,
                    ColumnCategory.ASSUME,
                    programRun = run,
                )
                val reset = ProgramVariable(
                    resetVariableP(row),
                    AnyBit.BOOL,
                    SMVTypes.BOOLEAN,
                    ColumnCategory.ASSUME,
                    programRun = run,
                )
                resetVariables[run to row] = reset.internalVariable(model.testTable.programRuns)
                setVariables[run to row] = set.internalVariable(model.testTable.programRuns)
                model.testTable.programVariables += set
                model.testTable.programVariables += reset
            }
        }

        val rows = model.testTable.region.flat()
        // translate backward(n)
        for (tableRow in rows) {
            for (entry in setVariables) {
                val (run, row) = entry.key
                val set = entry.value
                val isJumpTarget = tableRow.id == row
                tableRow.inputExpr[set.name] =
                    set.equal(if (isJumpTarget) SLiteral.TRUE else SLiteral.FALSE)

                if (isJumpTarget && !tableRow.duration.isOneStep) {
                    fail(
                        "The table row `${tableRow.id}? in table `${model.testTable.name}` is addressed by a backward-jump, " +
                            "but does not have the required of duration [1,1]. Please split up the row manually. ",
                    )
                }
            }

            val backwardCommands =
                tableRow.controlCommands.filterIsInstance<ControlCommand.Backward>()

            for ((k, reset) in resetVariables) {
                val (run, row) = k
                val resetActivated = null != backwardCommands.find {
                    it.affectedProgramRun == run && it.jumpToRow == row
                }
                tableRow.inputExpr[reset.name] = if (resetActivated) SLiteral.TRUE else SLiteral.FALSE
            }
        }
    }
}
