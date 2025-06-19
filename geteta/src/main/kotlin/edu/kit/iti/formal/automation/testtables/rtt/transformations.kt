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
package edu.kit.iti.formal.automation.testtables.rtt

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.Statements
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import edu.kit.iti.formal.automation.st0.trans.CodeTransformation

fun pauseVariableP() = "__PAUSE__"
fun pauseVariableTT(run: String): String = "${run}${pauseVariableP()}"
fun setVariableP(row: String) = "__SET_$row"
fun resetVariableP(row: String) = "__RESET_$row"
fun setVariableTT(row: String, run: String) = "${run}${setVariableP(row)}"
fun resetVariableTT(row: String, run: String) = "${run}${resetVariableP(row)}"

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.08.18)
 */
class RTTCodeAugmentation(skipSt0: Boolean, chapterMarks: Set<String>) : MultiCodeTransformation() {
    init {
        transformations += AddStuttering()
        if (!skipSt0) {
            transformations += SymbExFacade.getDefaultSimplifier()
        }
        transformations += AddSetAndReset(chapterMarks)
    }
}

private class AddSetAndReset(val chapterMarks: Set<String>) : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        val stateVariables = state.scope.variables.filter { !it.isInput }
        // val marks = gtt.chapterMarksForProgramRuns

        val newBody = StatementList()
        chapterMarks.forEach { row ->
            // new input variables
            val vdSet = VariableDeclaration(
                setVariableP(row),
                VariableDeclaration.INPUT,
                SimpleTypeDeclaration(AnyBit.BOOL, BooleanLit.LFALSE),
            )
            val vdReset = VariableDeclaration(
                resetVariableP(row),
                VariableDeclaration.INPUT,
                SimpleTypeDeclaration(AnyBit.BOOL, BooleanLit.LFALSE),
            )
            state.scope.add(vdSet)
            state.scope.add(vdReset)

            // body for storing and resetting the current state
            val setBody = StatementList()
            val resetBody = StatementList()

            stateVariables.forEach {
                // create a copy of this variable
                val storage = VariableDeclaration("${row}___${it.name}", it.type, it.typeDeclaration)
                    .also { new ->
                        new.dataType = it.dataType
                        // new.init = it.init
                        new.initValue = it.initValue
                    }
                state.scope.add(storage)

                setBody += storage.name assignTo it.name
                resetBody += it.name assignTo storage.name
            }

            newBody += Statements.ifthen(SymbolicReference(vdSet.name), setBody)
            newBody += Statements.ifthen(SymbolicReference(vdReset.name), resetBody)
        }
        newBody.add(state.stBody)
        state.stBody = newBody
        return state
    }
}

private class AddStuttering : CodeTransformation {

    override fun transform(state: TransformationState): TransformationState {
        addPauseVariable(state.scope)
        state.stBody = addIfStatement(state.stBody)
        return state
    }

    private fun addIfStatement(stBody: StatementList): StatementList {
        val s = StatementList()
        val ifStatement = IfStatement()
        ifStatement.addGuardedCommand(SymbolicReference(pauseVariableP()), StatementList())
        ifStatement.elseBranch = stBody
        s.add(ifStatement)
        return s
    }

    private fun addPauseVariable(scope: Scope) {
        val vd = VariableDeclaration(
            pauseVariableP(),
            VariableDeclaration.INPUT,
            SimpleTypeDeclaration(AnyBit.BOOL, BooleanLit.LFALSE),
        )
        scope.add(vd)
    }
}