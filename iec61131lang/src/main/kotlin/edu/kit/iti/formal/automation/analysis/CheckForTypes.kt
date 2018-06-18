package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

class CheckForTypes(private val reporter: Reporter) : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {}

    override fun visit(symbolicReference: SymbolicReference) {
        if (null == scope.getVariable(symbolicReference.identifier))
            reporter.report(
                    symbolicReference.startPosition,
                    "Could not find variable " + symbolicReference.identifier + ".",
                    "var-resolve", "error")
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        if (!functionDeclaration.returnType.isIdentified) {
            reporter.report(functionDeclaration.startPosition,
                    "Return type " + functionDeclaration.returnType.identifier + " not found.",
                    "type-resolve", "error")
        }
        super.visit(functionDeclaration)
    }

    override fun visit(invocation: InvocationStatement) {
        invocation.callee.accept(this)
    }

    override fun visit(invocation: Invocation) {
        invocation.callee.accept(this)
    }

    interface Reporter {
        fun report(position: Position, msg: String, category: String, error: String)
    }
}
