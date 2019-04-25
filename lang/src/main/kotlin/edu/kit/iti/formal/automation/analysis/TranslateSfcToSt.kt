package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.ActionDeclaration
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

object TranslateSfcToSt : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {}

    override fun visit(programDeclaration: ProgramDeclaration) {
        super.visit(programDeclaration)
        programDeclaration.sfcBody?.also {
            if (programDeclaration.stBody == null) {
                programDeclaration.stBody = IEC61131Facade
                        .translateToSt("", programDeclaration.scope, it)
            }
        }
    }

    override fun visit(actionDeclaration: ActionDeclaration) {
        actionDeclaration.sfcBody?.also {
            if (actionDeclaration.stBody == null) {
                actionDeclaration.stBody = IEC61131Facade.translateToSt(actionDeclaration.name, this.scope, it)
            }
        }
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        super.visit(functionBlockDeclaration)
        functionBlockDeclaration.sfcBody?.also {
            if (functionBlockDeclaration.stBody == null) {
                functionBlockDeclaration.stBody = IEC61131Facade.translateToSt("",
                        functionBlockDeclaration.scope, it)
            }
        }
    }


}