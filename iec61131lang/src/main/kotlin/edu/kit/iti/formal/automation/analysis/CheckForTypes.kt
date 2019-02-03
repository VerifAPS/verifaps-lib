package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.util.dlevenshtein
import org.antlr.v4.runtime.Token

/**
 * Similarity is defined via degree of levensthein of the low-case strings.
 * Percentage of changed characters.
 */
fun variableSimilarity(expected: String, defined: String): Double =
        dlevenshtein(expected.toLowerCase(), defined.toLowerCase()).toDouble() / expected.length

fun Iterable<String>.similarCandidates(reference: String, threshold: Double = .9) =
        this.map { it to variableSimilarity(reference, it) }
                .sortedByDescending { it.second }
                .filter { it.second > threshold }
                .map { it.first }


class CheckForTypes(private val reporter: Reporter) : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {}

    override fun visit(symbolicReference: SymbolicReference) {
        try {
            scope.getVariable(symbolicReference.identifier)
        } catch (e: VariableNotDefinedException) {
            val candidates = scope.allVisibleVariables.map { it.name }
                    .similarCandidates(symbolicReference.identifier)
                    .joinToString(", ")

            reporter.report(
                    node = symbolicReference,
                    message = "Could not find variable ${symbolicReference.identifier}. " +
                            "Possible candidates are: $candidates",
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
                   startLine: Int = -1,
                   startOffset: Int = -1,
                   endLine: Int = -1,
                   endOffset: Int = -1,
                   message: String = "",
                   category: String = "",
                   level: String = "") = report(ReporterMessage(
                sourceName, startLine, startOffset, endLine, endOffset, message, category, level))

        fun report(node: Top, message: String, category: String, level: String) = report(
                sourceName = node.ruleContext?.start?.tokenSource?.sourceName ?: "",
                startLine = node.startPosition.lineNumber,
                startOffset = node.startPosition.offset,
                endLine = node.endPosition.lineNumber,
                endOffset = node.endPosition.offset,
                message = message, category = category, level = level)

        fun report(node: Token?, message: String, category: String, level: String) = report(
                sourceName = node?.tokenSource?.sourceName ?: "",
                startLine = node?.line ?: 0,
                startOffset = node?.charPositionInLine ?: 0,
                endLine = (node?.line ?: 0) + (node?.text?.count { it == '\n' } ?: 0),
                endOffset = (node?.charPositionInLine ?: 0) + (node?.stopIndex ?: 0) - (node?.startIndex ?: 0),
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
        val startLine: Int = -1,
        val startOffset: Int = -1,
        val endLine: Int = -1,
        val endOffset: Int = -1,
        val message: String = "",
        val category: String = "",
        val level: String = "") {

    fun toHuman() =
            "[$level] $sourceName:$startLine:$startOffset $message [$category]"

    fun toJson() = toMap().toJson()

    fun toMap() =
            mapOf("level" to level.toUpperCase(),
                    "file" to sourceName,
                    "startLine" to startLine,
                    "startOffset" to startOffset,
                    "endLine" to endLine,
                    "endOffset" to endOffset,
                    "message" to message,
                    "category" to category)

}


fun <V> Map<String, V>.toJson(): String =
        this.entries.joinToString(", ", "{", "}") { (k, v) ->
            val a = when (v) {
                is String -> "\"${v.replace("\"", "\\\"")}\""
                else -> v.toString()
            }
            "\"${k}\" : $a"
        }