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
        scope.resolveFunction(invocation) ?: reporter.report(invocation.startPosition,
                "Return type ${invocation.callee} not found.",
                "function-resolve", "error")
    }

    override fun visit(variableDeclaration: VariableDeclaration) {
        variableDeclaration.initValue
                ?: reporter.report(variableDeclaration.startPosition, "Could not determine initial value for variable", "init-value", "error")

        variableDeclaration.dataType
                ?: reporter.report(variableDeclaration.startPosition, "Could not determine data type of variable", "type-resolve", "error")
    }

    interface Reporter {
        fun report(position: Position, msg: String, category: String, error: String)
    }
}
