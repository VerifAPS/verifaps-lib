package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.SimpleTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st.util.AstVisitor

object EnsureFunctionReturnValue : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}
    override fun visit(functionDeclaration: FunctionDeclaration) {
        val name = functionDeclaration.name
        if (name !in functionDeclaration.scope.variables) {
            functionDeclaration.scope.add(
                    VariableDeclaration(name, VariableDeclaration.OUTPUT,
                            SimpleTypeDeclaration(baseType = functionDeclaration.returnType.clone())))
        }
    }
}
