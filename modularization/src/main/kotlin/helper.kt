package edu.kit.iti.formal.automation.modularization

import edu.kit.iti.formal.automation.st.ast.Invocation
import edu.kit.iti.formal.automation.st.ast.InvocationStatement
import edu.kit.iti.formal.automation.st.ast.Top
import edu.kit.iti.formal.automation.st.util.AstVisitor

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.07.18)
 */
//
class SearchForInvocation : AstVisitor<Unit>() {
    var foundInvocation = false
    override fun defaultVisit(obj: Any) {}
    override fun visit(invocation: Invocation) {
        foundInvocation = true
    }

    override fun visit(invocation: InvocationStatement) {
        foundInvocation = true
    }
}

fun Top.containsInvocations(): Boolean {
    val sfi = SearchForInvocation()
    this.accept(sfi)
    return sfi.foundInvocation
}
//
