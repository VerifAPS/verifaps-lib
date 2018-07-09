package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

class CheckForTypes(private val reporter: Reporter) : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {}

    override fun visit(symbolicReference: SymbolicReference) {
        try {
            scope.getVariable(symbolicReference.identifier)
        } catch (e: VariableNotDefinedException) {
            reporter.report(
                    node = symbolicReference,
                    message = "Could not find variable " + symbolicReference.identifier + ".",
                    category = "var-resolve", level = "error")
        }
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        if (!functionDeclaration.returnType.isIdentified) {
            reporter.report(functionDeclaration,
                    "Return type " + functionDeclaration.returnType.identifier + " not found.",
                    "type-resolve", "error")
        }
        super.visit(functionDeclaration)
    }

    override fun visit(invocation: InvocationStatement) {
        invocation.callee.accept(this)
    }

    override fun visit(invocation: Invocation) {
        scope.resolveFunction(invocation) ?: reporter.report(invocation,
                "Return type ${invocation.callee} not found.",
                "function-resolve", "error")
    }

    override fun visit(variableDeclaration: VariableDeclaration) {
        variableDeclaration.initValue
                ?: reporter.report(variableDeclaration,
                        "Could not determine initial value for variable: ${variableDeclaration.name} with ${variableDeclaration.typeDeclaration}",
                        "init-value", "error")

        variableDeclaration.dataType
                ?: reporter.report(variableDeclaration,
                        "Could not determine data type of variable: ${variableDeclaration.name} with ${variableDeclaration.typeDeclaration}",
                        "type-resolve", "error")
    }


    interface Reporter {
        fun report(e: ReporterMessage)
        fun report(sourceName: String = "",
                   lineNumber: Int = -1,
                   charInLine: Int = -1,
                   message: String = "",
                   category: String = "",
                   level: String = "") = report(ReporterMessage(
                sourceName, lineNumber, charInLine, message, category, level))

        fun report(node: Top, message: String, category: String, level: String) = report(
                sourceName = node.ruleContext?.start?.tokenSource?.sourceName ?: "",
                lineNumber = node.startPosition.lineNumber,
                charInLine = node.startPosition.charInLine,
                message = message, category = category, level = level)
    }

    class DefaultReporter(val messages: MutableList<ReporterMessage> = ArrayList()) : Reporter {
        override fun report(e: ReporterMessage) {
            messages += e
        }
    }
}


data class ReporterMessage(
        val sourceName: String = "",
        val lineNumber: Int = -1,
        val charInLine: Int = -1,
        val message: String = "",
        val category: String = "",
        val level: String = "") {
    fun print() =
            "[$level] $sourceName:$lineNumber:$charInLine $message [$category]"
}

