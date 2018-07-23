package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import org.antlr.v4.runtime.Token

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
                    "Return type with name '${functionDeclaration.returnType.identifier}' for function declaration ${functionDeclaration.name} not found.",
                    "type-resolve", "error")
        }
        super.visit(functionDeclaration)
    }

    override fun visit(invocation: InvocationStatement) {
        invocation.invoked ?: reporter.report(invocation,
                "Invocation unresolved: ${invocation.callee}.",
                "invocation-resolve", "warn")
        //invocation.callee.accept(this)
    }

    override fun visit(invocation: Invocation) {
        val invoc = IEC61131Facade.print(invocation)
        scope.resolveFunction(invocation) ?: reporter.report(invocation,
                "Invocation $invoc could not resolved.",
                "function-resolve", "error")
    }

    override fun visit(variableDeclaration: VariableDeclaration) {
        variableDeclaration.initValue
                ?: reporter.report(variableDeclaration.token,
                        "Could not determine initial value for variable: ${variableDeclaration.name} with ${variableDeclaration.typeDeclaration}",
                        "init-value", "error")

        variableDeclaration.dataType
                ?: reporter.report(variableDeclaration.token,
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

        fun report(node: Top, message: String, category: String, level: String) = report(node.ruleContext?.start, message, category, level)

        fun report(node: Token?, message: String, category: String, level: String) = report(
                sourceName = node?.tokenSource?.sourceName ?: "",
                lineNumber = node?.line ?: 0,
                charInLine = node?.charPositionInLine ?: 0,
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

