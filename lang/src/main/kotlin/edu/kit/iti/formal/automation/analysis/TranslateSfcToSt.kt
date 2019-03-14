package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.ActionDeclaration
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
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
                actionDeclaration.stBody = IEC61131Facade.translateToSt(actionDeclaration.name,
                        this.scope, it)
            }
        }
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        super.visit(functionDeclaration)
        functionDeclaration.sfcBody?.also {
            if (functionDeclaration.stBody == null) {
                functionDeclaration.stBody = IEC61131Facade.translateToSt("",
                        functionDeclaration.scope, it)
            }
        }
    }


}