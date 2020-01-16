package edu.kit.iti.formal.automation.testtables.rtt

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.Statements
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import edu.kit.iti.formal.automation.st0.trans.CodeTransformation

const val VARIABLE_PAUSE: String = "__PAUSE__"
fun setVariable(row: String) = "__SET_$row"
fun resetVariable(row: String) = "__RESET_$row"


/**
 *
 * @author Alexander Weigl
 * @version 1 (04.08.18)
 */
class RTTCodeAugmentation(chapterMarks: Set<String>) : MultiCodeTransformation(
        AddStuttering(), AddSetAndReset(chapterMarks))

private class AddSetAndReset(val chapterMarks: Set<String>) : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        val stateVariables = state.scope.variables.filter { !it.isInput }
        //val marks = gtt.chapterMarksForProgramRuns

        val newBody = StatementList()
        chapterMarks.forEach { row ->
            // new input variables
            val vdSet = VariableDeclaration(setVariable(row), VariableDeclaration.INPUT,
                    SimpleTypeDeclaration(AnyBit.BOOL, BooleanLit.LFALSE))
            val vdReset = VariableDeclaration(resetVariable(row), VariableDeclaration.INPUT,
                    SimpleTypeDeclaration(AnyBit.BOOL, BooleanLit.LFALSE))
            state.scope.add(vdSet)
            state.scope.add(vdReset)

            //body for storing and resetting the current state
            val setBody = StatementList()
            val resetBody = StatementList()

            stateVariables.forEach {
                //create a copy of this variable
                val storage = it.copy(name = "${it.name}_${row}")
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
        val _if = IfStatement()
        _if.addGuardedCommand(SymbolicReference(VARIABLE_PAUSE), StatementList())
        _if.elseBranch = stBody
        s.add(_if)
        return s
    }

    private fun addPauseVariable(scope: Scope) {
        val vd = VariableDeclaration(VARIABLE_PAUSE, VariableDeclaration.INPUT,
                SimpleTypeDeclaration(AnyBit.BOOL, BooleanLit.LFALSE)
        )
        scope.add(vd)
    }
}
