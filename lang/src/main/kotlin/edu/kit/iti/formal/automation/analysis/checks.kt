package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.analysis.ReportCategory.*
import edu.kit.iti.formal.automation.analysis.ReportLevel.*
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.exceptions.DataTypeNotResolvedException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.util.dlevenshtein
import org.antlr.v4.runtime.Token
import java.lang.Throwable
import kotlin.math.ceil
import kotlin.math.log

fun getCheckers(reporter: Reporter) = listOf(CheckForTypes(reporter), CheckForLiterals(reporter), CheckForOO(reporter))

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
                reporter.report(literal,
                        "Value ${literal.value} not allowed in the enumeration type '$dt'. ",
                        DATATYPE_NOT_FOUND) {
                    candidates.addAll(dt.allowedValues.keys.similarCandidates(literal.value))
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

            reporter.report(symbolicReference,
                    "Could not find variable ${symbolicReference.identifier}. " +
                            "Possible candidates are: $candidates",
                    VARIABLE_NOT_RESOLVED)
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

        if (invocation.invoked != null) {
            //TODO check for recursive call
            //reporter.report(invocation, "Invocation unresolved: ${invocation.callee}.",
            //        INVOCATION_RESOLVE, WARN)
        }

        invocation.inputParameters.forEach {
            it.expression.accept(this@CheckForTypes)
            val dt = inferDataTypeOrNull(it.expression)
            val dtIn = invocation.invoked?.findInputVariable(it.name)

            if (dtIn == null) {
                reporter.report(it,
                        "Could not resolve data type for input variable: ${it.name}.",
                        VARIABLE_NOT_RESOLVED, ERROR)
            } else {
                if (dt != null) {
                    if (!dt.isAssignableTo(dtIn)) {
                        reporter.report(it,
                                "Type mismatch ($dt <= $dtIn)  for expression ${it.expression.toHuman()} and parameter ${it.name}.",
                                VARIABLE_NOT_RESOLVED, ERROR)
                    }
                }
            }
        }

        invocation.outputParameters.forEach {
            it.expression.accept(this@CheckForTypes)
            val ref = it.expression as? SymbolicReference
            if (ref == null) {
                reporter.report(it, "Only refs", INVOCATION_RESOLVE, WARN)
            } else {
                val dt = inferDataTypeOrNull(it.expression)
                val dtIn = invocation.invoked?.findInputVariable(it.name)

                if (dtIn == null) {
                    reporter.report(it,
                            "Could not resolve data type for input variable: ${it.name}.",
                            VARIABLE_NOT_RESOLVED, ERROR)
                } else {
                    if (dt != null) {
                        if (!dt.isAssignableTo(dtIn)) {
                            reporter.report(it,
                                    "Type mismatch ($dt <= $dtIn)  for expression ${it.expression.toHuman()} and parameter ${it.name}.",
                                    VARIABLE_NOT_RESOLVED, ERROR)
                        }
                    }
                }
            }
        }
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
            val exprTypes = invocation.parameters.map {
                try {
                    //val scope = invocation.invoked?.getCalleeScope()!!
                    it.expression.dataType(scope)
                } catch (e: VariableNotDefinedException) {
                    reporter.report(e.reference!!, "Variable ${e.reference.toHuman()} could not be found in scope.",
                            VARIABLE_NOT_RESOLVED)
                    null
                } catch (e: DataTypeNotResolvedException) {
                    reporter.report(e.expr, "Datatype of ${e.expr.toHuman()} could not be derived.",
                            TYPE_RESOLVE)
                    null
                }
            }

            if (expectedTypes.size != exprTypes.size) {
                val invoc = IEC61131Facade.print(invocation)
                reporter.report(invocation,
                        "Exptected function arguments ${expectedTypes.size}, but only ${exprTypes.size} given in function call: $invoc.",
                        ReportCategory.FUNCTIION_ARGUMENTS_MISMATCH)
            } else {
                expectedTypes.zip(exprTypes).forEach { (vd, def) ->
                    val exp = vd.dataType
                    if (exp != null) {
                        val c = def?.isAssignableTo(exp) ?: false
                        if (!c) {
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
        assignmentStatement.expression.accept(this)

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

        val lhsType = inferDataTypeOrNull(assignmentStatement.location, scope)
        val rhsType = inferDataTypeOrNull(assignmentStatement.expression, scope)

        if (lhsType != null && rhsType != null) {
            if (!rhsType.isAssignableTo(lhsType)) {
                reporter.report(assignmentStatement,
                        "Assignment type conflict between $rhsType and $lhsType",
                        ASSIGNMENT_TYPE_CONFLICT)
            }
        }
    }

    override fun visit(forStatement: ForStatement) {
        super.visit(forStatement)
    }

    private fun inferDataTypeOrNull(expr: Expression, s: Scope = scope): AnyDt? {
        return try {
            expr.dataType(s)
        } catch (e: VariableNotDefinedException) {
            reporter.report(e.reference!!,
                    "Could not resolve variable: ${e.reference.toHuman()}",
                    VARIABLE_NOT_RESOLVED)
            null
        } catch (e: DataTypeNotResolvedException) {
            reporter.report(expr, e.message!!, INFER)
            null
        }
    }
}

private fun Invoked?.findInputVariable(name: String?): AnyDt? {
    return if (name == null) null
    else when (this) {
        is Invoked.Program -> this.program.scope.variables[name]?.dataType
        is Invoked.FunctionBlock -> this.fb.scope.variables[name]?.dataType
        is Invoked.Function -> this.function.scope.variables[name]?.dataType
        is Invoked.Method -> this.method.scope.variables[name]?.dataType
        is Invoked.Action -> null
        null -> null
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
                            .filter { (_, m) -> m.name == method.name }
                            .joinToString { (w, m) -> "${w.name}.${m.name}" }
            reporter.report(method, "Method is declared as override, but does not override any method. Candidates are: $candidates")
        }

        if (method.isAbstract && !method.stBody.isEmpty()) {
            reporter.report(method, "Abstract method has a body.", ReportCategory.METHOD_HAS_BODY)
        }

    }
}

enum class ReportCategory {
    UNKNOWN, INFER,
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
fun Any?.toHuman(): String =
        when (this) {
            null -> "null"
            is SymbolicReference -> IEC61131Facade.print(this)
            is ClassDeclaration -> "class '$name'"
            is InterfaceDeclaration -> "interface '$name'"
            is MethodDeclaration -> "method '${parent?.name}.$name'"
            is Identifiable -> this.name
            else -> toString()
        }


class Reporter(val messages: MutableList<ReporterMessage> = ArrayList()) {
    fun getCaller(): String {
        val stackTrace = Throwable().stackTrace
        val firstNonReporterEntry = stackTrace.find {
            !it.className.startsWith(javaClass.name)
        }
        val caller = firstNonReporterEntry
        return if (caller == null) "" else caller.toString()
    }

    fun report(e: ReporterMessage) {
        messages += e
    }

    fun report(init: ReporterMessage.() -> Unit): ReporterMessage {
        val rm = ReporterMessage()
        init(rm)
        report(rm)
        return rm
    }

    fun report(node: Top?, msg: String, cat: ReportCategory = UNKNOWN,
               lvl: ReportLevel = ERROR, init: ReporterMessage.() -> Unit = {}) = report {
        position(node)
        message = msg
        category = cat
        level = lvl
        checkerId = getCaller()
        init(this)
    }

    fun report(node: Token?, msg: String, cat: ReportCategory,
               lvl: ReportLevel = ERROR, init: ReporterMessage.() -> Unit = {}) = report {
        position(node)
        message = msg
        category = cat
        level = lvl
        checkerId = getCaller()
        init(this)
    }
}


data class ReporterMessage(
        var sourceName: String = "",
        var message: String = "",
        var start: Position = Position(),
        var end: Position = Position(),
        var category: ReportCategory = UNKNOWN,
        var level: ReportLevel = ERROR,
        var candidates: MutableList<String> = arrayListOf(),
        var checkerId: String = "") {

    val length: Int
        get() = end.offset - start.offset + 1

    val startLine
        get() = start.lineNumber

    val endLine
        get() = end.lineNumber

    val startOffsetInLine
        get() = start.charInLine

    val endOffsetInLine
        get() = end.charInLine

    val startOffset
        get() = start.offset

    val endOffset
        get() = end.offset

    fun toHuman() =
            "[$level] $sourceName:$startLine:$startOffsetInLine $message [$category] ($checkerId)"

    fun toJson() = toMap().toJson()

    fun toMap() =
            mapOf("level" to level,
                    "file" to sourceName,
                    "startLine" to startLine,
                    "startOffsetInLine" to startOffsetInLine,
                    "endLine" to endLine,
                    "endOffsetInLine" to endOffsetInLine,
                    "message" to message,
                    "checkerId" to checkerId,
                    "category" to category)

    fun position(node: Token?) {
        sourceName = node?.tokenSource?.sourceName ?: ""
        if (node != null) {
            start = Position.start(node)
            end = Position.end(node)
        }
    }

    fun position(node: Top?) {
        sourceName = node?.ruleContext?.start?.tokenSource?.sourceName ?: ""
        if (node != null) {
            start = node.startPosition
            end = node.endPosition
        }
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
            "\"$k\" : $a"
        }