package edu.kit.iti.formal.automation.testtables

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import edu.kit.iti.formal.automation.st0.trans.CodeTransformation

val VARIABLE_PAUSE: String = "__PAUSE__"


/**
 *
 * @author Alexander Weigl
 * @version 1 (04.08.18)
 */
class RTTCodeAugmentation : MultiCodeTransformation(
        AddStuttering()
)

class AddStuttering : CodeTransformation {
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
