package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * This analysis sets an `stBody` generated from an `sfcBody`.
 * @author weigl
 * @author gorenflo
 */
class TranslateSfcToSt : AstVisitorWithScope<Unit>() {
    val newTypes = TypeDeclarations()

    override fun defaultVisit(obj: Any) {}

    override fun visit(programDeclaration: ProgramDeclaration) {
        super.visit(programDeclaration)
        programDeclaration.sfcBody?.also {
            if (programDeclaration.stBody == null) {
                val (t, st) = IEC61131Facade.translateSfcToSt(programDeclaration.scope, it, programDeclaration.name)
                programDeclaration.stBody = st
                newTypes.addAll(t)
            }
        }
    }

    override fun visit(actionDeclaration: ActionDeclaration) {
        actionDeclaration.sfcBody?.also {
            if (actionDeclaration.stBody == null) {
                val (t, st) = IEC61131Facade.translateSfcToSt(scope, it, "${actionDeclaration.name}_")
                actionDeclaration.stBody = st
                newTypes.addAll(t)
            }
        }
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        super.visit(functionBlockDeclaration)
        functionBlockDeclaration.sfcBody?.also {
            if (functionBlockDeclaration.stBody == null) {
                val (t, st) = IEC61131Facade.translateSfcToSt(
                        functionBlockDeclaration.scope, it, functionBlockDeclaration.name)
                functionBlockDeclaration.stBody = st
                newTypes.addAll(t)
            }
        }
    }
}