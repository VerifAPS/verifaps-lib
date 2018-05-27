package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import lombok.RequiredArgsConstructor

@RequiredArgsConstructor
class CheckForTypes : AstVisitor<Void> {
    private val reporter: Reporter? = null
    private var scope: Scope? = null

    override fun visit(symbolicReference: SymbolicReference): Void? {
        if (null == scope!!.getVariable(symbolicReference.identifier))
            reporter!!.report(
                    symbolicReference.startPosition,
                    "Could not find variable " + symbolicReference.identifier + ".",
                    "var-resolve", "error")
        return null    //super.visit(symbolicReference)
    }

    override fun visit(functionDeclaration: FunctionDeclaration): Void? {
        if (null == functionDeclaration.returnType) {
            reporter!!.report(functionDeclaration.startPosition,
                    "Return type " + functionDeclaration.returnTypeName + " not found.",
                    "type-resolve", "error")
        }
        super.visit(functionDeclaration)
        return null
    }

    override fun visit(localScope: Scope): Void? {
        scope = localScope
        super.visit(localScope)
        return null
    }

    override fun visit(invocation: InvocationStatement): Void? {
        invocation.callee.accept<Void>(this)

        return null
    }

    override fun visit(invocation: Invocation): Void? {
        invocation.callee.accept<Void>(this)
        return null
    }

    interface Reporter {
        fun report(position: Position, msg: String, category: String, error: String)
    }
}
