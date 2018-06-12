package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

class CheckForTypes : AstVisitorWithScope<Unit>() {
    private val reporter: Reporter? = null

    override fun visit(symbolicReference: SymbolicReference): Unit? {
        if (null == scope.getVariable(symbolicReference.identifier))
            reporter!!.report(
                    symbolicReference.startPosition,
                    "Could not find variable " + symbolicReference.identifier + ".",
                    "var-resolve", "error")
        return null    //super.visit(symbolicReference)
    }

    override fun visit(functionDeclaration: FunctionDeclaration): Unit? {
        if (!functionDeclaration.returnType.isIdentified) {
            reporter!!.report(functionDeclaration.startPosition,
                    "Return type " + functionDeclaration.returnType.identifier + " not found.",
                    "type-resolve", "error")
        }
        super.visit(functionDeclaration)
        return null
    }

    override fun visit(localScope: Scope): Unit? {
        super.visit(localScope)
        return null
    }

    override fun visit(invocation: InvocationStatement): Unit? {
        invocation.callee.accept(this)

        return null
    }

    override fun visit(invocation: Invocation): Unit? {
        invocation.callee.accept(this)
        return null
    }

    interface Reporter {
        fun report(position: Position, msg: String, category: String, error: String)
    }
}
