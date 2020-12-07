package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.il.Il2St
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

object TranslateIlToSt : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {}

    override fun visit(programDeclaration: ProgramDeclaration) {
        translate(programDeclaration)
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        translate(functionDeclaration)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        translate(functionBlockDeclaration)
    }

    private fun <T> translate(declaration: T) where  T : HasStBody, T : HasIlBody {
        declaration.ilBody?.let {
            if (declaration.stBody == null) {
                val il2St = Il2St(it)
                declaration.stBody = il2St.call().second
            }
        }
    }
}
