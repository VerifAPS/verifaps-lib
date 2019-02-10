package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.analysis.ReportCategory.*
import edu.kit.iti.formal.automation.analysis.ReportLevel.*
import edu.kit.iti.formal.automation.exceptions.DataTypeNotResolvedException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.util.dlevenshtein
import org.antlr.v4.runtime.Token
import kotlin.math.ceil
import kotlin.math.log

fun getCheckers(reporter: Reporter)
        = listOf(CheckForTypes(reporter), CheckForLiterals(reporter), CheckForOO(reporter))

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


class CheckForLiterals(private val reporter: Reporter) : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {}
    override fun visit(literal: Literal) {
        when (literal) {
            is IntegerLit -> check(literal)
            is StringLit -> check(literal)
            is RealLit -> check(literal)
            is EnumLit -> check(literal)
            is NullLit -> check(literal)
            is ToDLit -> check(literal)
            is DateLit -> check(literal)
            is TimeLit -> check(literal)
            is DateAndTimeLit -> check(literal)
            is BooleanLit -> check(literal)
            is BitLit -> check(literal)
            is UnindentifiedLit -> check(literal)
        }
    }

    private fun check(literal: EnumLit) {
        val dt = literal.dataType.obj
        if (dt == null) {
            reporter.report(literal,
                    "Could not find enumeration type '${literal.dataType.identifier}' for this literal",
                    DATATYPE_NOT_FOUND)
        } else {
            if (literal.value !in dt.allowedValues.keys) {
                reporter.report {
                    position(literal)
                    message = "Value ${literal.value} not allowed in the enumeration type '$dt'. "
                    candidates.addAll(dt.allowedValues.keys.similarCandidates(literal.value))
                    category = DATATYPE_NOT_FOUND
                }
            }
        }
    }

    private fun check(literal: ToDLit) {}

    private fun check(literal: DateLit) {
        if (literal.value.month !in 1..12) {
            reporter.report {
                position(literal)
                message = "Month not in range"
                category = UNKNOWN
            }
        }

        if (literal.value.day !in 1..12) {
            reporter.report {
                position(literal)
                message = "Day not in range"
                category = UNKNOWN
                error()
            }
        }
    }

    private fun check(literal: TimeLit) {}

    private fun check(literal: BooleanLit) {}

    private fun check(literal: DateAndTimeLit) {}

    private fun check(literal: BitLit) {
        literal.dataType.obj?.also {
            val bits = ceil(log(literal.value.toDouble(), 2.0))
            if (it.bitLength < bits) {
                reporter.report(literal, "Length exceeded")
            }
        }
    }

    private fun check(literal: UnindentifiedLit) {
        reporter.report(literal, "Unknown literal", LITERAL_UNKNOWN)
    }

    private fun check(literal: NullLit) {}

    private fun check(literal: RealLit) {}

    private fun check(literal: StringLit) {
        //TODO check for not defined escape characters
    }

    private fun check(literal: IntegerLit) {
        val value = literal.value
        val dt = literal.dataType(scope)
        if (!dt.isValid(value)) {
            reporter.report(literal, "The given integer literal is not in range for the specified data type: $dt",
                    LITERAL_RANGE_EXCEEDED, WARN)
        }
    }
}

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
                    category = VARIABLE_NOT_RESOLVED)
        }
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        if (!functionDeclaration.returnType.isIdentified) {
            reporter.report(functionDeclaration,
                    "Return type with name '${functionDeclaration.returnType.identifier}' for function DECLARATION ${functionDeclaration.name} not found.",
                    TYPE_RESOLVE)
        }
        super.visit(functionDeclaration)
    }

    override fun visit(invocation: InvocationStatement) {
        invocation.invoked ?: reporter.report(invocation,
                "Invocation unresolved: ${invocation.callee}.",
                INVOCATION_RESOLVE, WARN)
        //invocation.callee.accept(this)
    }

    override fun visit(invocation: Invocation) {
        val fd = scope.resolveFunction(invocation)
        if (fd == null) {
            val invoc = IEC61131Facade.print(invocation)
            reporter.report(invocation,
                    "Invocation $invoc could not resolved.",
                    FUNCTION_RESOLVE)
        } else {
            val expectedTypes = fd.scope.variables.filter { it.isInput }
            val exprTypes = invocation.parameters.map { it.expression.dataType(scope) }

            if (expectedTypes.size != exprTypes.size) {
                val invoc = IEC61131Facade.print(invocation)
                reporter.report(invocation,
                        "Exptected function arguments ${expectedTypes.size}, but only ${exprTypes.size} given in function call: $invoc.",
                        ReportCategory.FUNCTIION_ARGUMENTS_MISMATCH)
            } else {
                expectedTypes.zip(exprTypes).forEach { (vd, def) ->
                    val exp = vd.dataType
                    if (exp != null) {
                        if (!def.isAssignableTo(exp)) {
                            reporter.report(invocation,
                                    "Type mismatch for argument ${vd.name}: exptected ${exp} but got ${def}",
                                    ReportCategory.FUNCTION_CALL_TYPE_MISMATCH)
                        }
                    }
                }
            }
        }
    }

    override fun visit(variableDeclaration: VariableDeclaration) {
        variableDeclaration.initValue
                ?: reporter.report(variableDeclaration.token,
                        "Could not determine initial value for variable: ${variableDeclaration.name} with ${variableDeclaration.typeDeclaration}",
                        ReportCategory.INIT_VALUE)

        variableDeclaration.dataType
                ?: reporter.report(variableDeclaration.token,
                        "Could not determine data type of variable: ${variableDeclaration.name} with ${variableDeclaration.typeDeclaration}",
                        ReportCategory.TYPE_RESOLVE)
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        try {
            val vd = scope.getVariable(assignmentStatement.location)
            if (vd.isInput || vd.isConstant) {
                reporter.report(assignmentStatement.location, "Variable not writable",
                        PERMISSION, WARN)
            }
        } catch (e: VariableNotDefinedException) {
            reporter.report(assignmentStatement.location,
                    "Could not resolve ${assignmentStatement.location.toHuman()}.",
                    VARIABLE_NOT_RESOLVED)
        }

        try {
            val lhsType = assignmentStatement.location.dataType(scope)
            val rhsType = assignmentStatement.expression.dataType(scope)
            if (!rhsType.isAssignableTo(lhsType)) {
                reporter.report(assignmentStatement,
                        "Assignment type conflict between $rhsType and $lhsType",
                        ASSIGNMENT_TYPE_CONFLICT)
            }
        } catch (e: VariableNotDefinedException) {
            reporter.report(e.reference!!,
                    "Could not resolve variable.",
                    PERMISSION)
        } catch (e: DataTypeNotResolvedException) {
            reporter.report(assignmentStatement.expression,
                    e.message!!, PERMISSION)
        }
    }
}

class CheckForOO(private val reporter: Reporter) : AstVisitorWithScope<Unit>() {
    private var clazz: ClassDeclaration? = null
    private var interfaze: InterfaceDeclaration? = null

    override fun defaultVisit(obj: Any) {}

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        interfaze = interfaceDeclaration
        interfaceDeclaration.interfaces.forEach {
            it.obj ?: reporter.report(interfaceDeclaration, "Could not resolve interface ${it.identifier}.",
                    ReportCategory.INTERFACE_NOT_RESOLVED)
        }
    }

    override fun visit(clazz: ClassDeclaration) {
        this.clazz = clazz

        clazz.interfaces.forEach {
            it.obj ?: reporter.report(clazz, "Could not resolve interface ${it.identifier}.",
                    ReportCategory.INTERFACE_NOT_RESOLVED)
        }

        if (clazz.parent.obj == null && clazz.parent.identifier != null)
            reporter.report(clazz, "Could not resolve parent class ${clazz.parent.identifier}.",
                    ReportCategory.CLASS_NOT_RESOLVED)


        val declM = clazz.declaredMethods
        val defM = clazz.definedMethods
        for ((where, declared) in declM) {
            if (!defM.any { it.second sameSignature declared }) {
                reporter.report(clazz,
                        "Declared method ${declared.toHuman()} in ${where.toHuman()} " +
                                "is not defined in ${clazz.toHuman()}.",
                        ReportCategory.METHOD_NOT_DEFINED,
                        ERROR)
            }
        }
    }

    override fun visit(method: MethodDeclaration) {
        if (method.isOverride && method.overrides == null) {
            val candidates =
                    (if (clazz != null)
                        (clazz!!.declaredMethods + clazz!!.definedMethods)
                    else interfaze!!.definedMethods)
                            .filter { (w, m) -> m.name == method.name }
                            .joinToString { (w, m) -> "${w.name}.${m.name}" }
            reporter.report(method, "Method is declared as override, but does not override any method. Candidates are: $candidates")
        }

        if (method.isAbstract && !method.stBody.isEmpty()) {
            reporter.report(method, "Abstract method has a body.", ReportCategory.METHOD_HAS_BODY)
        }

    }
}

enum class ReportCategory {
    UNKNOWN,
    DATATYPE_NOT_FOUND,
    LITERAL_UNKNOWN,
    LITERAL_RANGE_EXCEEDED,
    VARIABLE_NOT_RESOLVED,
    INVOCATION_RESOLVE,
    TYPE_RESOLVE,
    DECLARATION,
    FUNCTION_RESOLVE,
    FUNCTIION_ARGUMENTS_MISMATCH,
    FUNCTION_CALL_TYPE_MISMATCH,
    INIT_VALUE,
    PERMISSION,
    METHOD_NOT_DEFINED,
    ASSIGNMENT_TYPE_CONFLICT,
    INTERFACE_NOT_RESOLVED,
    CLASS_NOT_RESOLVED,
    METHOD_HAS_BODY,
    SYNTAX

}

enum class ReportLevel {
    INFO, WARN, ERROR
}

/**
 *
 */
private fun Any?.toHuman(): String =
        when (this) {
            null -> "null"
            is ClassDeclaration -> "class '$name'"
            is InterfaceDeclaration -> "interface '$name'"
            is MethodDeclaration -> "method '${parent?.name}.$name'"
            is Identifiable -> this.name
            else -> toString()
        }


class Reporter(val messages: MutableList<ReporterMessage> = ArrayList()) {
    fun report(e: ReporterMessage) {
        messages += e
    }

    fun report(init: ReporterMessage.() -> Unit) {
        val rm = ReporterMessage()
        init(rm)
        report(rm)
    }

    fun report(sourceName: String = "",
               startLine: Int = -1,
               startOffset: Int = -1,
               endLine: Int = -1,
               endOffset: Int = -1,
               message: String = "",
               category: ReportCategory = UNKNOWN,
               level: ReportLevel = ERROR) = report(ReporterMessage(
            sourceName, startLine, startOffset, endLine, endOffset, message, category, level))

    fun report(node: Top, message: String, category: ReportCategory = UNKNOWN,
               level: ReportLevel = ERROR) = report(
            sourceName = node.ruleContext?.start?.tokenSource?.sourceName ?: "",
            startLine = node.startPosition.lineNumber,
            startOffset = node.startPosition.offset,
            endLine = node.endPosition.lineNumber,
            endOffset = node.endPosition.offset,
            message = message, category = category, level = level)

    fun report(node: Token?, message: String, category: ReportCategory,
               level: ReportLevel = ERROR) = report(
            sourceName = node?.tokenSource?.sourceName ?: "",
            startLine = node?.line ?: 0,
            startOffset = node?.charPositionInLine ?: 0,
            endLine = (node?.line ?: 0) + (node?.text?.count { it == '\n' } ?: 0),
            endOffset = (node?.charPositionInLine ?: 0) + (node?.stopIndex ?: 0) - (node?.startIndex ?: 0),
            message = message, category = category, level = level)
}


data class ReporterMessage(
        var sourceName: String = "",
        var startLine: Int = -1,
        var startOffset: Int = -1,
        var endLine: Int = -1,
        var endOffset: Int = -1,
        var message: String = "",
        var category: ReportCategory = UNKNOWN,
        var level: ReportLevel = ERROR,
        var candidates: MutableList<String> = arrayListOf()) {

    fun toHuman() =
            "[$level] $sourceName:$startLine:$startOffset $message [$category]"

    fun toJson() = toMap().toJson()

    fun toMap() =
            mapOf("level" to level,
                    "file" to sourceName,
                    "startLine" to startLine,
                    "startOffset" to startOffset,
                    "endLine" to endLine,
                    "endOffset" to endOffset,
                    "message" to message,
                    "category" to category)

    fun position(node: Token?) {
        sourceName = node?.tokenSource?.sourceName ?: ""
        startLine = node?.line ?: 0
        startOffset = node?.charPositionInLine ?: 0
        endLine = (node?.line ?: 0) + (node?.text?.count { it == '\n' } ?: 0)
        endOffset = (node?.charPositionInLine ?: 0) + (node?.stopIndex ?: 0) - (node?.startIndex ?: 0)
    }

    fun position(node: Top?) {
        sourceName = node?.ruleContext?.start?.tokenSource?.sourceName ?: ""
        startLine = node?.startPosition?.lineNumber ?: -1
        startOffset = node?.startPosition?.offset ?: 0
        endLine = node?.endPosition?.lineNumber ?: -1
        endOffset = node?.endPosition?.offset ?: 0
    }

    fun error() {
        level = ERROR
    }

    fun warn() {
        level = WARN
    }

    fun info() {
        level = INFO
    }
}


fun <V> Map<String, V>.toJson(): String =
        this.entries.joinToString(", ", "{", "}") { (k, v) ->
            val a = when (v) {
                is String -> "\"${v.replace("\"", "\\\"")}\""
                else -> v.toString()
            }
            "\"${k}\" : $a"
        }