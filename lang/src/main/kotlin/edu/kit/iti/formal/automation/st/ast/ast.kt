package edu.kit.iti.formal.automation.st.ast

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.analysis.toHuman
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.exceptions.DataTypeNotResolvedException
import edu.kit.iti.formal.automation.exceptions.IECException
import edu.kit.iti.formal.automation.exceptions.TypeConformityException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.fbd.FbdBody
import edu.kit.iti.formal.automation.il.IlBody
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.*
import edu.kit.iti.formal.automation.st.Cloneable
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.automation.visitors.Visitor
import edu.kit.iti.formal.util.HasMetadata
import edu.kit.iti.formal.util.Metadata
import edu.kit.iti.formal.util.times
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import java.io.Serializable
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*
import java.util.function.Consumer
import kotlin.collections.ArrayList
import kotlin.collections.HashMap
import kotlin.reflect.full.memberProperties

sealed class Top : Visitable, Cloneable, HasMetadata,
        HasRuleContext, Serializable {
    override var ruleContext: ParserRuleContext? = null

    val nodeName: String
        get() = this::class.simpleName!!

    val children: List<Top>
        get() =
            this::class.memberProperties
                    .map {
                        it.getter.call(this)
                    }
                    .filterIsInstance<Top>()
                    .map { it as Top }

    private var _metadata: Metadata? = null
    override fun metadata(create: Boolean): Metadata? {
        if (create && _metadata == null)
            _metadata = Metadata()
        return _metadata
    }
}

interface HasScope {
    var scope: Scope
}

interface HasPragma {
    val pragmas: MutableList<Pragma>
    fun findAttributePragma(name: String) = findPragma<Pragma.Attribute>().find { it.name == name }
}

inline fun <reified T> HasPragma.findPragma() = pragmas.filterIsInstance<T>()


//region Declaration and Toplevel
abstract class PouElement : Top(), Identifiable, HasPragma, Comparable<PouElement> {
    var comment: String = ""
    override fun compareTo(other: PouElement): Int {
        return name.compareTo(other.name)
    }

    override val pragmas: MutableList<Pragma> by lazy { arrayListOf<Pragma>() }
}

data class PouElements(val elements: MutableList<PouElement> = arrayListOf())
    : Top(), MutableList<PouElement> by elements, Visitable {
    override fun <T> accept(visitor: Visitor<T>) = visitor.visit(this)
    override fun clone() = copy()

    companion object {
        fun singleton(pd: PouElement): PouElements {
            val tle = PouElements()
            tle.elements.add(pd)
            return tle
        }
    }
}

data class Namespace(var fqName: String) {
    val name: String
        get() = nameParts.last()

    val nameParts: Sequence<String>
        get() = fqName.splitToSequence('.')

    infix fun isSubSpaceOf(n: Namespace): Boolean {
        if (this == n || fqName == n.fqName)
            return false
        return n.fqName.startsWith(fqName)
    }

}

val GLOBAL_NAMESPACE = Namespace("")

data class NamespaceDeclaration(
        var fqName: Namespace = GLOBAL_NAMESPACE,
        val pous: PouElements = PouElements(),
        override var scope: Scope = Scope()) : HasScope, Top() {
    override fun clone(): NamespaceDeclaration {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class ConfigurationDeclaration(override var scope: Scope) : HasScope, PouElement() {
    override fun clone(): Top {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override val name: String = "<configuration>"
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class RefList<T : Identifiable>(private var impl: ArrayList<RefTo<T>> = arrayListOf()) : MutableList<RefTo<T>> by impl,
        Cloneable {
    fun add(element: String) = add(RefTo(element))

    override fun clone(): RefList<T> {
        val list = RefList<T>()
        forEach { list += it.clone() }
        return list
    }

    override fun toString() = impl.toString()
}

val ANONYM = "ANONYM"

data class FunctionBlockDeclaration(
        override var name: String = ANONYM,
        override var scope: Scope = Scope(),
        override var stBody: StatementList? = null,
        override var sfcBody: SFCImplementation? = null,
        override var ilBody: IlBody? = null,
        override var fbBody: FbdBody? = null,
        var actions: LookupList<ActionDeclaration> = ArrayLookupList(),
        override val interfaces: RefList<InterfaceDeclaration> = RefList(),
        override val methods: MutableList<MethodDeclaration> = arrayListOf()
) : PouExecutable(), HasMethods, Classifier {

    var parent: RefTo<FunctionBlockDeclaration> = RefTo()
    var isFinal: Boolean = false
    var isAbstract: Boolean = false

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): FunctionBlockDeclaration = copy()

    fun addAction(act: ActionDeclaration) {
        this.actions.add(act)
    }

    fun setParentName(parentName: String) {
        parent.identifier = parentName
    }
}

data class ResourceDeclaration(override var scope: Scope) : HasScope, PouElement() {
    override val name: String
        get() = "<resource>"

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone() = copy()
}

data class ClassDeclaration(
        override var name: String = ANONYM,
        override var scope: Scope = Scope(),
        var isFinal: Boolean = false,
        var isAbstract: Boolean = false,
        override val interfaces: RefList<InterfaceDeclaration> = RefList(),
        override val methods: MutableList<MethodDeclaration> = arrayListOf(),
        val parent: RefTo<ClassDeclaration> = RefTo<ClassDeclaration>()) :
        HasInterfaces, HasScope, HasMethods, PouElement(), Classifier {


    override fun clone() = copy()
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

interface HasInterfaces : Identifiable {
    val interfaces: RefList<InterfaceDeclaration>
}

data class TypeDeclarations(private val declarations: MutableList<TypeDeclaration> = arrayListOf())
    : PouElement(), MutableList<TypeDeclaration> by declarations {

    override val name: String get() = "types"

    constructor(vararg stp: TypeDeclaration) : this() {
        declarations.addAll(Arrays.asList<TypeDeclaration>(*stp))
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): TypeDeclarations {
        val td = TypeDeclarations()
        cloneList(td, this)
        return rctxHelper(td, this)
    }

    fun declares(typeName: String): Boolean {
        for (td in this) {
            if (td.name == typeName)
                return true
        }
        return false
    }
}


interface HasStBody {
    var stBody: StatementList?
}

interface HasSfcBody {
    var sfcBody: SFCImplementation?
}

interface HasIlBody {
    var ilBody: IlBody?
}

interface HasFbBody {
    var fbBody: FbdBody?
}

interface HasBody : HasSfcBody, HasStBody, HasIlBody, HasFbBody

interface HasMethods : Identifiable {
    val methods: MutableList<MethodDeclaration>
}

abstract class PouExecutable : PouElement(), HasScope, HasBody, Visitable {
    abstract override fun clone(): PouExecutable
}


data class ProgramDeclaration(
        override var name: String = ANONYM,
        override var scope: Scope = Scope(),
        override var stBody: StatementList? = null,
        override var sfcBody: SFCImplementation? = null,
        override var ilBody: IlBody? = null,
        override var fbBody: FbdBody? = null,
        var actions: LookupList<ActionDeclaration> = ArrayLookupList()
) : PouExecutable(), Identifiable {
    override fun clone() = copy()
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    fun addAction(act: ActionDeclaration) {
        this.actions.add(act)
    }
}

class InterfaceDeclaration(
        override var name: String = "",
        override var interfaces: RefList<InterfaceDeclaration> = RefList(),
        override var methods: MutableList<MethodDeclaration> = arrayListOf()
) : HasInterfaces, HasMethods, PouElement(), Identifiable, Classifier {


    override fun clone(): InterfaceDeclaration {
        val i = InterfaceDeclaration()
        i.name = name
        methods.forEach { method -> i.methods.add(method.clone()) }
        interfaces.forEach { intf -> i.interfaces.add(intf.clone()) }
        return i
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is InterfaceDeclaration) return false

        if (name != other.name) return false
        if (interfaces != other.interfaces) return false
        if (methods != other.methods) return false

        return true
    }

    override fun hashCode(): Int {
        var result = name.hashCode()
        result = 31 * result + interfaces.hashCode()
        result = 31 * result + methods.hashCode()
        return result
    }
}

data class FunctionDeclaration(
        override var name: String = ANONYM,
        override var scope: Scope = Scope(),
        var returnType: RefTo<AnyDt> = RefTo(),
        override var stBody: StatementList? = StatementList(),
        override var ilBody: IlBody? = null,
        override var fbBody: FbdBody? = null)
    : PouExecutable() {

    override var sfcBody: SFCImplementation?
        get() = null
        set(value) {
            throw IllegalStateException("Functions are not allowed to be an SFC. Internal would be required")
        }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): FunctionDeclaration {
        val fd = FunctionDeclaration()
        fd.scope = scope.clone()
        fd.name = this.name
        fd.returnType = returnType.clone()
        fd.stBody = stBody?.clone()
        return fd
    }
}

data class GlobalVariableListDeclaration(
        override var scope: Scope = Scope())
    : HasScope, PouElement() {

    override val name: String = "VAR_GLOBAL"
    override fun clone() = copy()
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class MethodDeclaration(
        override var name: String = ANONYM,
        var returnType: RefTo<AnyDt> = RefTo(),
        var stBody: StatementList = StatementList()
) : HasScope, Top(), Identifiable {

    var accessSpecifier: AccessSpecifier = AccessSpecifier.PROTECTED
    var isFinal: Boolean = false
    var isAbstract: Boolean = false
    var isOverride: Boolean = false
    var parent: Classifier? = null
    var overrides: Pair<HasMethods, MethodDeclaration>? = null

    override var scope: Scope = Scope()

    var returnTypeName: String?
        get() = if (returnType.identifier == null) "VOID" else returnType.identifier
        set(rt) {
            returnType.identifier = rt
        }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): MethodDeclaration {
        val md = MethodDeclaration()
        md.accessSpecifier = accessSpecifier
        md.isAbstract = isAbstract
        md.isFinal = isFinal
        md.isOverride = isOverride
        md.scope = scope.clone()
        md.name = this.name
        md.returnType = returnType.clone()
        return md
    }
}
//endregion

//region Statements
object EMPTY_EXPRESSION : Expression() {
    override fun dataType(localScope: Scope): AnyDt = throw IllegalStateException()
    override fun clone(): Expression = EMPTY_EXPRESSION
    override fun <T> accept(visitor: Visitor<T>) = visitor.visit(this);
}

abstract class Statement : Top(), HasPragma {
    abstract override fun clone(): Statement
    override val pragmas: MutableList<Pragma> by lazy { arrayListOf<Pragma>() }
}


data class RepeatStatement(var condition: Expression = EMPTY_EXPRESSION, var statements: StatementList = StatementList()) : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): RepeatStatement {
        val rs = RepeatStatement()
        rs.ruleContext = ruleContext
        rs.condition = (condition.clone())
        rs.statements = (statements.clone())
        return rs
    }
}

data class WhileStatement(var condition: Expression = EMPTY_EXPRESSION, var statements: StatementList = StatementList()) : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): WhileStatement {
        val ws = WhileStatement()
        ws.ruleContext = ruleContext
        ws.condition = condition.clone()
        ws.statements = statements.clone()
        return ws
    }
}

data class AssignmentStatement(var location: SymbolicReference,
                               var expression: Expression = EMPTY_EXPRESSION,
                               var reference: Boolean = false) : Statement() {

    var isAssignmentAttempt: Boolean = false

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): AssignmentStatement {
        val a = AssignmentStatement(location.clone(), expression.clone()
                //Utils.copyNull<Reference>(location),
                //Utils.copyNull<Expression>(expression)
        )
        a.reference = reference
        a.isAssignmentAttempt = isAssignmentAttempt
        a.ruleContext = ruleContext
        return a
    }
}

data class CaseStatement(
        var expression: Expression = EMPTY_EXPRESSION,
        var cases: MutableList<Case> = arrayListOf(),
        var elseCase: StatementList = StatementList())
    : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    fun addCase(cs: Case) {
        cases.add(cs)
    }


    override fun clone(): CaseStatement {
        val c = CaseStatement()
        c.ruleContext = ruleContext
        c.expression = expression.clone()
        cases.forEach { cs -> c.addCase(cs.clone()) }
        c.elseCase = elseCase.clone()
        return c
    }
}

data class Case(
        var conditions: MutableList<CaseCondition> = arrayListOf(),
        var statements: StatementList = StatementList()
) : Top() {

    fun addCondition(condition: CaseCondition) = conditions.add(condition)

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): Case {
        val c = Case()
        cloneList(c.conditions, conditions)
        c.statements = statements.clone()
        return c
    }
}

class ExitStatement : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): Statement {
        val es = ExitStatement()
        es.ruleContext = ruleContext
        return es
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ExitStatement) return false
        return true
    }

    override fun hashCode(): Int {
        return 23423532
    }


    companion object {
        var EXIT_STATMENT = ExitStatement()
    }
}

data class JumpStatement(var target: String) : Statement() {
    override fun clone() = copy().also { it.ruleContext = ruleContext }
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class LabelStatement(var label: String) : Statement() {
    override fun clone() = copy().also { it.ruleContext = ruleContext }
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}


class ReturnStatement : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): ReturnStatement {
        val rt = ReturnStatement()
        rt.ruleContext = ruleContext
        return rt
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ReturnStatement) return false
        return true
    }

    override fun hashCode(): Int {
        return 696996
    }

}

data class ForStatement(
        var variable: String = ANONYM,
        var start: Expression = EMPTY_EXPRESSION,
        var stop: Expression = EMPTY_EXPRESSION,
        var step: Expression? = null,
        var statements: StatementList = StatementList()) : Statement() {

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): Statement {
        val fs = ForStatement()
        fs.ruleContext = ruleContext
        fs.variable = variable
        fs.start = start.clone()
        fs.stop = stop.clone()
        fs.step = step?.clone()
        fs.statements = statements.clone()
        return fs
    }
}

data class CommentStatement(var comment: String) : Statement() {
    constructor(format: String, vararg args: Any) : this(String.format(format, *args)) {}

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): CommentStatement {
        return CommentStatement(comment).also { it.copyMetaFrom(this) }
    }

    companion object {
        fun box(s: String, vararg args: Any): Statement {
            val q = String.format(s, *args)
            val rest = "*" * (79 - 2 - q.length)
            val line = "*" * 79
            return CommentStatement(
                    "$line\n * $q $rest\n $line")
        }

        fun single(fmt: String, vararg args: Any): Statement {
            return CommentStatement(fmt, *args)
        }
    }
}

/**
 * This is a very special statement, and allows to add arbitrary information
 * into AST, for example special statements for symbolic execution.
 *
 * @see
 */
sealed class SpecialStatement : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    data class Assert(var exprs: MutableList<Expression>,
                      val name: String? = null) : SpecialStatement() {
        override fun clone() = Assert(exprs.clone())
    }

    data class Assume(var exprs: MutableList<Expression>,
                      val name: String? = null) : SpecialStatement() {
        override fun clone() = Assume(exprs.clone())
    }

    data class Havoc(var variables: MutableList<SymbolicReference>,
                     val name: String? = null) : SpecialStatement() {
        override fun clone() = Havoc(variables.clone())
    }
}


data class GuardedStatement(
        var condition: Expression,
        var statements: StatementList = StatementList()) : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): GuardedStatement {
        val gs = GuardedStatement(condition.clone(), statements.clone())
        gs.ruleContext = ruleContext
        return gs
    }
}

data class IfStatement(
        val conditionalBranches: MutableList<GuardedStatement> = arrayListOf(),
        var elseBranch: StatementList = StatementList()
) : Statement() {
    fun addGuardedCommand(expr: Expression?, statements: StatementList): GuardedStatement {
        if (expr == null)
            throw IllegalArgumentException()
        val e = GuardedStatement(expr, statements)
        conditionalBranches.add(e)
        return e
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    fun addGuardedCommand(gc: GuardedStatement) {
        conditionalBranches.add(gc)
    }

    override fun clone(): IfStatement {
        val stmt = IfStatement()
        cloneList(stmt.conditionalBranches, conditionalBranches)
        stmt.elseBranch = this.elseBranch.clone()
        return rctxHelper(stmt, this)
    }
}

data class InvocationStatement(
        var callee: SymbolicReference = SymbolicReference(),
        var parameters: MutableList<InvocationParameter> = arrayListOf()) : Statement(), HasPragma {
    var invoked: Invoked? = null


    val inputParameters: List<InvocationParameter>
        get() = parameters.filter { !it.isOutput }

    val outputParameters: List<InvocationParameter>
        get() = parameters.filter { it.isOutput }

    override val pragmas: MutableList<Pragma> by lazy { arrayListOf<Pragma>() }

    constructor(fnName: String, vararg expr: Expression)
            : this(SymbolicReference(fnName), expr.map { InvocationParameter(it) }.toMutableList())

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): InvocationStatement {
        val f = InvocationStatement()
        f.callee = callee.clone()
        f.parameters = parameters.map { it.clone() }.toMutableList()
        f.invoked = invoked
        return f
    }
}
// endregion


//region Expressions
abstract class Expression : Top() {
    @Throws(VariableNotDefinedException::class, TypeConformityException::class, DataTypeNotResolvedException::class)
    abstract fun dataType(localScope: Scope = Scope.defaultScope()): AnyDt

    abstract override fun clone(): Expression

    infix fun and(right: Expression): Expression = BinaryExpression(this, Operators.AND, right)
    infix fun or(right: Expression): Expression = BinaryExpression(this, Operators.OR, right)
    infix fun plus(right: Expression): Expression = BinaryExpression(this, Operators.ADD, right)
    infix fun minus(right: Expression): Expression = BinaryExpression(this, Operators.SUB, right)
    infix fun times(right: Expression): Expression = BinaryExpression(this, Operators.MULT, right)
    infix fun div(right: Expression): Expression = BinaryExpression(this, Operators.DIV, right)

    infix fun eq(right: Expression): Expression = BinaryExpression(this, Operators.EQUALS, right)
    infix fun neq(right: Expression): Expression = BinaryExpression(this, Operators.NOT_EQUALS, right)
    infix fun le(right: Expression): Expression = BinaryExpression(this, Operators.LESS_EQUALS, right)
    infix fun lt(right: Expression): Expression = BinaryExpression(this, Operators.LESS_THAN, right)
    infix fun ge(right: Expression): Expression = BinaryExpression(this, Operators.GREATER_EQUALS, right)
    infix fun gt(right: Expression): Expression = BinaryExpression(this, Operators.GREATER_THAN, right)

    operator fun not() = UnaryExpression(Operators.NOT, this)
    fun unaryMinus() = UnaryExpression(Operators.MINUS, this)

}

data class BinaryExpression(
        var leftExpr: Expression,
        var operator: BinaryOperator,
        var rightExpr: Expression
) : Expression() {

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    override fun dataType(localScope: Scope): AnyDt {
        val a = leftExpr.dataType(localScope)
        val b = rightExpr.dataType(localScope)
        val c = operator.getDataType(a, b) ?: throw TypeConformityException(
                this, operator.expectedDataTypes, a, b
        )
        return c
    }

    override fun clone(): Expression {
        val be = BinaryExpression(leftExpr.clone(),
                operator, rightExpr.clone())
        be.ruleContext = ruleContext
        return be
    }
}

data class UnaryExpression(
        var operator: UnaryOperator,
        var expression: Expression) : Expression() {

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    override fun dataType(localScope: Scope): AnyDt {
        val a = operator.getPromotedType(expression.dataType(localScope))
        if (a == null) {
            throw TypeConformityException(this, operator.expectedDataTypes, a)
        }
        return a
    }

    override fun clone(): UnaryExpression {
        val ue = UnaryExpression(operator, expression.clone())
        ue.ruleContext = ruleContext
        return ue
    }
}

data class SymbolicReference @JvmOverloads constructor(
        var identifier: String = ANONYM,
        var subscripts: ExpressionList? = null,
        var sub: SymbolicReference? = null
//        var dataType: AnyDt? = null
) : Reference() {

    var derefCount = 0

    val isArrayAccess: Boolean
        get() = subscripts != null

    constructor(s: String?, sub: SymbolicReference? = null) : this() {
        if (s == null)
            throw IllegalArgumentException()
        this.sub = sub
        identifier = s
    }

    fun addSubscript(ast: Expression) {
        if (subscripts == null)
            subscripts = ExpressionList()
        subscripts!!.add(ast)
    }

    fun hasSub(): Boolean {
        return sub != null
    }

    fun hasSubscripts(): Boolean {
        return subscripts != null
    }


    fun asList(): List<SymbolicReference> {
        val list = ArrayList<SymbolicReference>()
        if (sub != null)
            list.addAll(sub!!.asList())
        list.add(0, this)
        return list
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)


    @Throws(VariableNotDefinedException::class)
    override fun dataType(scope: Scope): AnyDt {
        try {
            return scope.getVariable(this).dataType!!
        } catch (e: Exception) {
            throw VariableNotDefinedException(scope, this)
        }
    }


    override fun clone(): SymbolicReference {
        val sr = SymbolicReference()
        sr.ruleContext = ruleContext
        sr.identifier = identifier
        sr.subscripts = subscripts?.clone()
        sr.sub = sub?.clone()
        sr.derefCount = derefCount
        //sr.dataType = dataType
        return sr
    }

    fun toPath(): List<String> {
        val l = ArrayList<String>(10)
        var cur: SymbolicReference = this
        while (true) {
            l.add(cur.identifier)
            if (cur.hasSub()) cur = cur.sub!!
            else break
        }
        return l
    }

    /*
    override fun toString(): String {
        return (getIdentifier()
                + Strings.repeat("^", derefCount)
                + (if (subscripts != null) subscripts!!.toString() else "")
                + if (sub == null) "" else "." + sub!!.toString())
    }*/
}


data class Invocation(
        var callee: SymbolicReference = SymbolicReference(),
        val parameters: MutableList<InvocationParameter> = arrayListOf()
) : Expression() {
    var invoked: Invoked? = null

    val inputParameters: List<InvocationParameter>
        get() = parameters.filter { it.isInput }

    val outputParameters: List<InvocationParameter>
        get() = parameters.filter { it.isOutput }

    var calleeName: String
        get() = callee.identifier
        set(calleeName) {
            callee = SymbolicReference(calleeName)
        }

    constructor(calleeName: String) : this() {
        callee.identifier = calleeName
    }

    constructor(calleeName: String, vararg expr: Expression) : this() {
        callee.identifier = calleeName
        for (e in expr) {
            parameters.add(InvocationParameter(e))
        }
    }

    @Deprecated("")
    constructor(invocation: Invocation) : this() {
        callee = invocation.callee
        parameters.addAll(invocation.parameters)
    }

    constructor(calleeName: String, expr: List<Expression>) : this() {
        callee.identifier = calleeName
        for (e in expr) {
            parameters.add(InvocationParameter(e))
        }
    }

    constructor(function: FunctionDeclaration) : this() {
        callee = SymbolicReference(function.name)
    }

    fun addParameter(parameter: InvocationParameter) {
        parameters.add(parameter)
        //parameters.sortWith { a,b -> obj.compareTo(o) }
    }

    fun addParameters(parameterList: List<InvocationParameter>) {
        parameters.addAll(parameterList)
        //parameters.sort(Comparator<InvocationParameter> { obj, o -> obj.compareTo(o) })
    }

    fun addExpressionParameters(expressionList: List<Expression>) {
        expressionList.forEach { e -> parameters.add(InvocationParameter(e)) }
        //parameters.sort(Comparator<InvocationParameter> { obj, o -> obj.compareTo(o) })
    }


    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    @Throws(DataTypeNotResolvedException::class)
    override fun dataType(localScope: Scope): AnyDt {
        val invoked = invoked
        return if (invoked != null) {
            when (invoked) {
                is Invoked.Program -> throw DataTypeNotResolvedException("Invocation calls to a program. Programs have no return types")
                is Invoked.FunctionBlock -> throw DataTypeNotResolvedException("Invocation calls to a FB. FB have no return types")
                is Invoked.Action -> throw DataTypeNotResolvedException("Invocation calls to an action. Action have no return types")
                is Invoked.Function -> invoked.function.returnType.obj
                        ?: throw DataTypeNotResolvedException("Return type of function ${invoked.function} is not resolved")
                is Invoked.Method -> invoked.method.returnType.obj
                        ?: throw DataTypeNotResolvedException("Return type of method ${invoked.method} is not resolved")
            }
        } else {
            throw DataTypeNotResolvedException("Call to function ${callee.toHuman()} could not be resolved.")
        }
    }

    override fun clone(): Invocation {
        val fc = Invocation(calleeName)
        fc.ruleContext = ruleContext
        fc.callee = callee.clone()
        cloneList(fc.parameters, parameters)
        return fc
    }

}

data class InvocationParameter(
        var name: String? = null,
        var isOutput: Boolean = false,
        var expression: Expression = EMPTY_EXPRESSION
) : Top(), Comparable<InvocationParameter> {
    val isInput: Boolean
        get() = !isOutput

    constructor(expr: Expression) : this(expression = expr)

    override fun clone() = InvocationParameter(this.name, isOutput, this.expression.clone())

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    override operator fun compareTo(o: InvocationParameter): Int {
        return if (o.name != null)
            this.name!!.compareTo(o.name!!)
        else
            0
    }
}

//region Type
interface TypeDeclaration : HasRuleContext, Identifiable, Visitable, Cloneable {
    override var name: String

    //var dataType: AnyDt
    @property:Deprecated("should be an type DECLARATION")
    var baseType: RefTo<AnyDt>
    val initialization: Initialization?
    override fun clone(): TypeDeclaration

    @Throws(IECException::class)
    fun getDataType(scope: Scope): AnyDt? =
            this.accept(TypeDeclarationToDataType(scope))

    fun setInit(initialization: Initialization?)
}

/**
 *
 */
data class SimpleTypeDeclaration(
    override var name: String = ANONYM,
    @Deprecated("should be an type DECLARATION")
    override var baseType: RefTo<AnyDt> = RefTo(),
    override var initialization: Initialization? = null
) : TypeDeclaration, Top() {
    constructor(dt: AnyDt, init: Initialization?) : this(baseType = RefTo(dt), initialization = init)

    override fun setInit(init: Initialization?) {
        this.initialization = init
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): SimpleTypeDeclaration {
        val std = SimpleTypeDeclaration()
        std.name = name
        std.baseType = baseType.clone()
        std.ruleContext = (ruleContext)
        std.initialization = initialization?.clone()
        return std
    }
}

data class StructureTypeDeclaration(
    override var name: String = ANONYM,
    @Deprecated("should be an type DECLARATION")
    override var baseType: RefTo<AnyDt> = RefTo(),
    override var initialization: StructureInitialization? = null,
    var fields: VariableScope = VariableScope()
) : TypeDeclaration, Top() {
    override fun setInit(init: Initialization?) {
        initialization = init as StructureInitialization?
    }

    constructor(typeName: String, fields: List<VariableDeclaration>) : this() {
        name = typeName
        fields.forEach(Consumer<VariableDeclaration> { this.fields.add(it) })
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): StructureTypeDeclaration {
        val t = StructureTypeDeclaration()
        t.ruleContext = ruleContext
        t.initialization = initialization?.clone()
        t.fields = fields.clone()
        t.baseType = baseType.clone()
        return t
    }


    fun addField(text: String, accept: TypeDeclaration): VariableDeclaration {
        val vd = VariableDeclaration(text, 0, accept)
        fields.add(vd)
        return vd
    }
}

data class SubRangeTypeDeclaration(
    override var name: String = ANONYM,
    @Deprecated("should be an type DECLARATION")
    override var baseType: RefTo<AnyDt> = RefTo(),//TODO false, should be type DECLARATION
    override var initialization: IntegerLit? = null,
    var range: Range? = null)
    : TypeDeclaration, Top() {

    override fun setInit(init: Initialization?) {
        initialization = init as? IntegerLit
    }

    /*override fun getDataType(scope: Scope): RangeType? {
        val start = Integer.valueOf(range!!.start.text)
        val stop = Integer.valueOf(range!!.stop.text)
        assert(start <= stop)
        val rt = RangeType(typeName, start, stop, super.getDataType(scope) as AnyInt)
        setDataType(rt)
        return rt
    }*/

    override fun clone(): SubRangeTypeDeclaration {
        val t = SubRangeTypeDeclaration()
        t.range = range?.clone()
        t.baseType = baseType.clone()
        t.initialization = initialization?.clone()
        return t
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class EnumerationTypeDeclaration(
    override var name: String = ANONYM,
    @Deprecated("should be an type DECLARATION")
    override var baseType: RefTo<AnyDt> = RefTo(),
    override var initialization: IdentifierInitializer? = null
) : TypeDeclaration, Top() {
    override fun clone(): EnumerationTypeDeclaration {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    var allowedValues: MutableList<Token> = LinkedList()
    var values: MutableList<Int> = ArrayList()
    private var counter: Int = 0

    override fun setInit(init: Initialization?) {
        initialization = init as IdentifierInitializer?
    }


    init {
        baseType.identifier = "ENUM"
    }


    override fun <S> accept(visitor: Visitor<S>): S = visitor.visit(this)

    fun addValue(text: Token) {
        allowedValues.add(text)
        values.add(counter)
        counter += 1
    }

    override fun getDataType(scope: Scope) = super.getDataType(scope) as EnumerateType

    /*//TODO rework
    val init = allowedValues[0].text
    if (initialization != null) {
        if (initialization!!.dataType isType EnumerateType) {
            val value = initialization!!.asValue()
            //init = value;
        } else if (initialization!!.dataType isType AnyInt) {
            val value = initialization!!.asValue() as Values.VAnyInt
            //init = allowedValues.get(value);
        }
    }

    val et = EnumerateType(getTypeName(),
            allowedValues.stream().map<String>(Function<Token, String> { it.getText() }).collect<List<String>, Any>(Collectors.toList()),
            init)
    baseType = (et)
    return et
override fun clone(): EnumerationTypeDeclaration {
    val etd = EnumerationTypeDeclaration()
    etd.allowedValues = ArrayList(allowedValues)
    etd.counter = counter
    etd.baseType = baseType
    etd.baseTypeName = baseTypeName
    etd.values = ArrayList(values)
    etd.typeName = typeName
    return etd
}
*/

    fun setInt(value: IntegerLit) {
        val v = value.value.toInt()
        values[values.size - 1] = v
        counter = v + 1
    }
}

data class ArrayTypeDeclaration(
        override var name: String = ANONYM,
        var type: TypeDeclaration,
        override var initialization: ArrayInitialization? = null,
        val ranges: MutableList<Range> = arrayListOf())
    : TypeDeclaration, Top() {
    @Deprecated("should be an type DECLARATION")
    override var baseType = RefTo<AnyDt>()

    override fun setInit(init: Initialization?) {
        initialization = init as ArrayInitialization?
    }


    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): ArrayTypeDeclaration {
        val atd = ArrayTypeDeclaration(
                name, type.clone(), initialization?.clone()
        )
        atd.ruleContext = ruleContext
        cloneList(atd.ranges, ranges)
        atd.baseType = baseType.clone()
        return atd
    }

    fun addSubRange(ast: Range) {
        ranges.add(ast)
    }

    /*
    override fun getDataType(scope: Scope): AnyDt? {
        if (type != null)
            return type
        baseType = (scope.resolveDataType(baseTypeName!!))
        type = ArrayType(getTypeName(), baseType, ranges)
        return type
    }
    */
}

class StringTypeDeclaration(
    override var name: String = ANONYM,
    @Deprecated("should be an type DECLARATION")
    override var baseType: RefTo<AnyDt> = RefTo(),
    var size: Literal? = null,
    override var initialization: Literal? = null)
    : TypeDeclaration, Top() {

    override fun setInit(init: Initialization?) {
        initialization = init as Literal?
    }


    override fun clone(): StringTypeDeclaration {
        val t = StringTypeDeclaration()
        t.initialization = initialization?.clone()
        t.baseType = baseType.clone()
        t.size = size?.clone()
        return t
    }

    override fun <S> accept(visitor: Visitor<S>): S = visitor.visit(this)
}

class PointerTypeDeclaration(
    override var name: String = ANONYM,
    @Deprecated("should be an type DECLARATION")
    override var baseType: RefTo<AnyDt> = RefTo(),
    override var initialization: Literal? = null)
    : TypeDeclaration, Top() {

    override fun setInit(init: Initialization?) {
        initialization = init as Literal?
    }

    override fun <S> accept(visitor: Visitor<S>): S = visitor.visit(this)
    override fun clone() = rctxHelper(PointerTypeDeclaration(name, baseType.clone(), initialization?.clone()), this)
}

data class ReferenceTypeDeclaration(
    override var name: String = ANONYM,
    var refTo: SimpleTypeDeclaration = SimpleTypeDeclaration(),
    @Deprecated("should be an type DECLARATION")
    override var baseType: RefTo<AnyDt> = refTo.baseType)
    : TypeDeclaration, Top() {
    override var initialization: Literal? = null

    override fun setInit(init: Initialization?) {
        initialization = init as Literal?
    }


    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): ReferenceTypeDeclaration {
        val rs = ReferenceTypeDeclaration()
        rs.refTo = refTo
        rs.baseType = baseType
        return rs
    }
}
//endregion


//region Initialization
abstract class Initialization : Expression() {
    abstract override fun clone(): Initialization
    fun getValue(): Value<*, *> = accept(EvaluateInitialization)
}

data class ArrayInitialization(
        val initValues: MutableList<Initialization> = arrayListOf())
    : Initialization() {

    override fun dataType(localScope: Scope): AnyDt {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): ArrayInitialization {
        val a = ArrayInitialization()
        initValues.forEach { i -> a.initValues.add(i.clone()) }
        a.ruleContext = ruleContext
        return a
    }
}

data class StructureInitialization(
        //var structureName: String? = null
        var initValues: MutableMap<String, Initialization> = HashMap())
    : Initialization() {

    constructor(initEntries: List<Map.Entry<String, Initialization>>) : this() {
        initEntries.forEach { entry -> addField(entry.key, entry.value) }
    }

    fun addField(s: String, init: Initialization) {
        initValues[s] = init
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    override fun dataType(localScope: Scope): AnyDt {
        TODO()
    }

    override fun clone(): StructureInitialization {
        val st = StructureInitialization()
        cloneMap(st.initValues, initValues)
        return st
    }
}

class IdentifierInitializer(var enumType: EnumerateType? = null,
                            var value: String? = null) : Initialization() {

    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    override fun dataType(localScope: Scope): AnyDt {
        return enumType!!
    }

    override fun clone() = rctxHelper(IdentifierInitializer(enumType, value), this)

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}
//endregion


abstract class CaseCondition() : Top() {
    data class Range(var range: edu.kit.iti.formal.automation.st.ast.Range) : CaseCondition() {
        var start: Literal? = null
        var stop: Literal? = null

        override fun <T> accept(visitor: Visitor<T>): T {
            return visitor.visit(this)
        }

        override fun clone(): Range {
            val r = Range(range.copy())
            r.start = start?.clone()
            r.stop = stop?.clone()
            r.ruleContext = (ruleContext)
            return r
        }
    }

    data class IntegerCondition(var value: IntegerLit) : CaseCondition() {
        override fun <T> accept(visitor: Visitor<T>): T {
            return visitor.visit(this)
        }

        override fun clone(): IntegerCondition {
            return IntegerCondition(this.value.clone())
        }
    }

    data class Enumeration(var start: EnumLit, var stop: EnumLit? = null) : CaseCondition() {
        constructor(start: EnumLit) : this(start, start)

        override fun <T> accept(visitor: Visitor<T>): T {
            return visitor.visit(this)
        }

        override fun clone(): Enumeration {
            val e = Enumeration(start.clone(), stop?.clone())
            e.ruleContext = (ruleContext)
            return e
        }
    }
}

class Deref(val reference: Reference) : Reference() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun dataType(localScope: Scope): AnyDt {
        return reference.dataType(localScope)//TODO
    }

    override fun clone(): Deref {
        return Deref(reference.clone())
    }
}

class DirectVariable(s: String) : Reference() {


    override fun <T> accept(visitor: Visitor<T>): T {
        throw IllegalStateException("not implemented")
    }


    override fun dataType(localScope: Scope): AnyDt {
        throw IllegalStateException("not implemented")
    }

    override fun clone(): Reference {
        return DirectVariable("todo")
    }

}

sealed class Invoked {
    fun getCalleeScope(): Scope? {
        return when (this) {
            is Program -> program.scope
            is FunctionBlock -> fb.scope
            is Function -> function.scope
            is Method -> method.scope
            is Action -> scope
        }
    }

    class Program(val program: ProgramDeclaration) : Invoked()
    class FunctionBlock(val fb: FunctionBlockDeclaration) : Invoked()
    class Function(val function: FunctionDeclaration) : Invoked()
    class Method(val method: MethodDeclaration, val onClass: ClassDataType) : Invoked()
    class Action(val action: ActionDeclaration, val scope: Scope) : Invoked()
}

sealed class Literal() : Initialization() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    abstract fun asValue(scope: Scope = Scope.defaultScope()): Value<*, *>?
    abstract override fun clone(): Literal
}

data class IntegerLit(var dataType: RefTo<AnyInt> = RefTo<AnyInt>(INT),
                      var value: BigInteger) : Literal() {
    constructor(dt: String?, v: BigInteger) : this(RefTo(dt), v)
    constructor(dt: AnyInt, v: BigInteger) : this(RefTo(dt), v)
    constructor(intVal: VAnyInt) : this(intVal.dataType, intVal.value)
    constructor(value: Int) : this(INT, value.toBigInteger())

    override fun dataType(localScope: Scope) = dataType.checkAndresolveDt(localScope, INT)

    override fun asValue(scope: Scope) = VAnyInt(dataType(scope), value)
    override fun clone() = copy()
}


data class StringLit(var dataType: RefTo<IECString> = RefTo(), var value: String) : Literal() {
    constructor(dt: IECString, v: String) : this(RefTo(dt.name, dt), v)

    override fun dataType(localScope: Scope) = dataType.obj ?: IECString.STRING
    override fun asValue(scope: Scope) = VIECString(dataType(scope), value)
    override fun clone() = copy()
}

data class RealLit(var dataType: RefTo<AnyReal> = RefTo(), var value: BigDecimal) : Literal() {
    constructor(dt: AnyReal, v: BigDecimal) : this(RefTo(dt), v)
    constructor(dt: String?, v: BigDecimal) : this(RefTo(dt), v)

    override fun dataType(localScope: Scope) = dataType.checkAndresolveDt(localScope, AnyReal.REAL)

    override fun asValue(scope: Scope) = VAnyReal(dataType(scope), value)
    override fun clone() = copy()
}

private fun <T : AnyDt> RefTo<T>.checkAndresolveDt(localScope: Scope, default: T? = null): T {
    obj?.let { return it }
    resolve { localScope.resolveDataType0(it) }
    if (obj == null) return default ?: throw DataTypeNotResolvedException("Datatype of ${identifier} is not defined")
    else return obj!!
}

data class EnumLit(var dataType: RefTo<EnumerateType> = RefTo(), var value: String) : Literal() {
    constructor(dataType: EnumerateType, value: String) : this(RefTo(dataType), value)
    constructor(dataType: String?, value: String) : this(RefTo(dataType), value)

    override fun dataType(localScope: Scope) = dataType.checkAndresolveDt(localScope)
    override fun asValue(scope: Scope) = VAnyEnum(dataType.obj!!, value)
    override fun clone() = copy()
}

class NullLit() : Literal() {
    override fun clone() = rctxHelper(NullLit(), this)
    override fun dataType(localScope: Scope) = ClassDataType.AnyClassDt
    override fun asValue(scope: Scope) = VNULL
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is NullLit) return false
        return true
    }

    override fun hashCode(): Int {
        return javaClass.hashCode()
    }

}

data class ToDLit(var value: TimeofDayData) : Literal() {
    override fun dataType(localScope: Scope) = AnyDate.TIME_OF_DAY
    override fun asValue(scope: Scope) = VTimeOfDay(AnyDate.TIME_OF_DAY, value)
    override fun clone() = copy()
}

data class DateLit(var value: DateData) : Literal() {
    override fun dataType(localScope: Scope) = AnyDate.DATE
    override fun asValue(scope: Scope) = VDate(AnyDate.DATE, value)
    override fun clone() = copy()
}

data class TimeLit(var value: TimeData) : Literal() {
    override fun dataType(localScope: Scope) = TimeType.TIME_TYPE
    override fun asValue(scope: Scope) = VTime(dataType(scope), value)
    override fun clone() = copy()
}

data class DateAndTimeLit(var value: DateAndTimeData) : Literal() {
    override fun dataType(localScope: Scope) = AnyDate.DATE_AND_TIME
    override fun asValue(scope: Scope) = VDateAndTime(dataType(scope), value)
    override fun clone() = copy()
}

data class BooleanLit(var value: Boolean) : Literal() {
    companion object {
        val LFALSE = BooleanLit(false)
        val LTRUE = BooleanLit(true)
    }

    override fun asValue(localScope: Scope) = if (value) TRUE else FALSE
    override fun dataType(scope: Scope) = AnyBit.BOOL
    override fun clone() = copy()
}

data class BitLit(var dataType: RefTo<AnyBit> = RefTo(), var value: Long) : Literal() {
    constructor(dt: AnyBit, v: Long) : this(RefTo(dt), v)
    constructor(dt: String?, v: Long) : this(RefTo(dt), v)

    override fun dataType(localScope: Scope) = dataType.checkAndresolveDt(localScope)
    override fun asValue(scope: Scope) = VAnyBit(dataType.obj!!, Bits(value, dataType.obj!!.bitLength))
    override fun clone() = copy()
}

data class UnindentifiedLit(var value: String) : Literal() {
    override fun asValue(localScope: Scope) = null
    override fun dataType(scope: Scope) = throw DataTypeNotResolvedException("Datatype of UnindentifiedLit is not defined")
    override fun clone() = copy()
}

class Location : Expression {
    internal var path: MutableList<Reference> = ArrayList(5)

    constructor() {}
    constructor(path: MutableList<Reference>) {
        this.path = path
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    fun add(ast: Reference) {
        path.add(ast)
    }

    fun lastDeref() {
        val deref = Deref(path[path.size - 1])
        path.removeAt(path.size - 1)
        path.add(deref)
    }


    fun asIdentifier(): String {
        return path.stream().map { a -> a.toString() }.reduce("") { a, b -> "$a.$b" }
    }


    override fun dataType(localScope: Scope): AnyDt {
        TODO("Not implemented")
    }

    override fun clone(): Location {
        val l = Location()
        cloneList(l.path, path)
        l.ruleContext = ruleContext
        return l
    }
}


//region Helpers
open class StatementList(private val list: MutableList<Statement> = arrayListOf())
    : Statement(), MutableList<Statement> by list {

    constructor(vararg then: Statement) : this(list = ArrayList(Arrays.asList(*then)))

    constructor(statements: StatementList) : this() {
        addAll(statements)
    }

    constructor(ts: Collection<Statement>) : this() {
        this.list.addAll(ts)
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    fun comment(format: String, vararg args: Any) {
        add(CommentStatement(format, *args))
    }

    override fun toString() = list.toString()


    //override fun clone(): StatementList = StatementList(map { it.clone() })

    override fun clone(): StatementList {
        val s = StatementList()
        forEach { s.add(it.clone()) }
        return s
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is StatementList) return false
        if (list != other.list) return false
        return true
    }

    override fun hashCode(): Int {
        return list.hashCode()
    }
}

data class ExpressionList(private val expressions: MutableList<Expression> = arrayListOf())
    : Top(), MutableList<Expression> by expressions {

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): ExpressionList {
        val el = ExpressionList()
        forEach { e -> el.add(e.clone()) }
        return el
    }
}

data class Position(
        val lineNumber: Int = -1,
        val charInLine: Int = -1,
        val offset: Int = -1,
        val file: String = "") : Cloneable {

    companion object {
        fun start(token: Token?) =
                Position(token?.line ?: -1,
                        token?.charPositionInLine ?: -1,
                        token?.startIndex ?: -1,
                        token?.tokenSource?.sourceName ?: "")

        fun end(token: Token?): Position {
            return if (token == null) Position()
            else {
                val text = token.text ?: ""
                val newlines = text.count { it == '\n' }
                Position(token.line + newlines,
                        text.length - Math.max(0, text.lastIndexOf('\n')),
                        token.stopIndex, token?.tokenSource?.sourceName ?: "")
            }
        }
    }

    override fun clone() = copy()

    override fun toString(): String = "@$lineNumber:$charInLine"
}
//endregion 

data class BlockStatement(var name: String = "empty",
                          var statements: StatementList = StatementList(),
                          var state: MutableList<SymbolicReference> = arrayListOf(),
                          var input: MutableList<SymbolicReference> = arrayListOf(),
                          var output: MutableList<SymbolicReference> = arrayListOf()) : Statement() {
    /** Fully qualified call stack, seperated with dots */
    var fqName: String = name

    /** number of invocation */
    var number: Int = 0

    /** if generated by a function block, this field is set*/
    var originalInvoked: Invoked? = null

    /** human readable field for specifying call sites*/
    fun repr() = "$fqName.$number"

    /** end comment to be printed */
    val commentEnd
        get() = CommentStatement("END_REGION $name (${input.joinToString(", ")}) => (${output.joinToString(", ")})")

    /** start comment to be printed */
    val commentStart
        get() = CommentStatement("REGION $name (${input.joinToString(", ")}) => (${output.joinToString(", ")})")

    override fun clone(): BlockStatement {
        val bs = BlockStatement(name, statements.clone(), state.clone(), input.clone(), output.clone())
        bs.originalInvoked = originalInvoked
        bs.fqName = fqName
        bs.number = number
        return bs
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

private fun <T : Cloneable> Iterable<T>.clone(): MutableList<T> = map { it.clone() as T }.toMutableList()

abstract class Reference : Initialization() {
    abstract override fun clone(): Reference
}

class VariableBuilder(val scope: VariableScope) {
    private val stack = Stack<Int>()
    private val pragmaStack = Stack<List<Pragma>>()
    private var initialization: Initialization? = null
    private var identifiers: MutableList<Token> = arrayListOf()
    private var type: TypeDeclaration? = null


    //region Handling of special flags (like constant, input or global)
    fun popPragma() = pragmaStack.pop()
    fun pushPragma(p: List<Pragma>): VariableBuilder {
        pragmaStack.push(p)
        return this
    }

    fun clear(): VariableBuilder {
        identifiers = ArrayList()
        return this
    }

    fun pop(): VariableBuilder {
        stack.pop()
        return this
    }

    fun peek(): Int {
        try {
            return stack.peek()
        } catch (e: EmptyStackException) {
            return 0
        }

    }

    fun push(input: Int): VariableBuilder {
        stack.push(input)
        return this
    }

    fun clear(i: Int): VariableBuilder {
        stack.clear()
        stack.push(i)
        return this
    }

    fun mix(i: Int): VariableBuilder {
        push(stack.pop() or i)
        return this
    }
    //endregion

    fun boolType(): VariableBuilder {
        return type("BOOL")
    }

    fun pointerType(pointsTo: String): VariableBuilder {
        return type(PointerTypeDeclaration(pointsTo))
    }

    fun stringType(base: String,
                   length: Literal,
                   def: Literal): VariableBuilder {
        val std = StringTypeDeclaration()
        std.baseType.identifier = base
        std.size = length
        std.initialization = def
        return type(std)
    }


    fun baseType(baseType: String) = type(baseType)

    private fun type(baseType: String): VariableBuilder {
        val td = SimpleTypeDeclaration(baseType)
        td.baseType.identifier = baseType
        return type(td)
    }


    fun type(type: TypeDeclaration): VariableBuilder {
        this.type = type
        return this
    }

    fun setInitialization(initialization: Initialization): VariableBuilder {
        this.initialization = initialization
        return this
    }

    fun pragma(): List<Pragma>? {
        if (pragmaStack.isEmpty()) return null
        return pragmaStack.reduce { acc, list -> acc + list }
    }

    fun create(): VariableBuilder {
        for (id in identifiers) {
            val vd = VariableDeclaration(id.text.trim('`'), peek(), type!!)
            vd.token = id
            pragma()?.run { forEach { vd.pragmas += it.clone() } }
            this.scope.add(vd)
        }
        return this
    }


    fun close(): VariableBuilder {
        return create().clear()
    }


    fun identifiers(ast: List<Token>): VariableBuilder {
        identifiers.clear()
        identifiers.addAll(ast)
        return this
    }

    fun identifiers(ast: Token): VariableBuilder {
        identifiers.clear()
        identifiers.add(ast)
        return this
    }
}

data class VariableDeclaration(
        override var name: String = ANONYM,
        var type: Int = 0
) : Top(), Comparable<VariableDeclaration>, Identifiable, HasPragma {

    override val pragmas: MutableList<Pragma> by lazy { arrayListOf<Pragma>() }


    var typeDeclaration: TypeDeclaration? = null

    /**
     * determined by the typeDeclaration
     */
    var dataType: AnyDt? = null

    val init: Initialization?
        get() = typeDeclaration?.initialization
    /*set(init) {
        typeDeclaration?.initialization = init
    }*/

    val isRetain: Boolean
        get() = isType(RETAIN)


    val isConstant: Boolean
        get() = isType(CONSTANT)


    val isExternal: Boolean
        get() = isType(EXTERNAL)


    val isTemp: Boolean
        get() = isType(TEMP)


    val isLocated: Boolean
        get() = isType(LOCATED)


    val isLocal: Boolean
        get() = isType(LOCAL)


    val isOutput: Boolean
        get() = isType(OUTPUT)


    val isInput: Boolean
        get() = isType(INPUT)

    val isInOut: Boolean
        get() = isInput && isOutput

    val isGlobal: Boolean
        get() = isType(GLOBAL)

    val isPublic: Boolean
        get() = isType(PUBLIC)

    val isInternal: Boolean
        get() = isType(INTERNAL)

    val isProtected: Boolean
        get() = isType(PROTECTED)

    val isPrivate: Boolean
        get() = isType(PRIVATE)

    var initValue: Value<*, *>? = null

    var token: Token? = null

    override val startPosition: Position
        get() = Position.start(token)

    override val endPosition: Position
        get() = Position.end(token)

    constructor(name: String, type: Int, td: TypeDeclaration?) : this(name, type) {
        typeDeclaration = td
    }

    constructor(name: String, td: TypeDeclaration) : this() {
        this.name = name
        typeDeclaration = td
    }

    constructor(name: String, dataType: AnyDt) : this(name, SimpleTypeDeclaration()) {
        this.dataType = dataType
        this.typeDeclaration = SimpleTypeDeclaration()
        (this.typeDeclaration as SimpleTypeDeclaration).baseType.obj = dataType
    }

    constructor(value: VariableDeclaration) : this(value.name, value.type, value.typeDeclaration!!) {
        dataType = value.dataType
        typeDeclaration = value.typeDeclaration
    }

    /*
    constructor(name: String, flags: Int, td: TypeDeclaration) : this(name, td) {
        type = flags
    }*/

    constructor(name: String, flags: Int, dt: AnyDt) : this(name, dt) {
        type = flags
        initValue = DefaultInitValue.getInit(dt)
    }

    fun isType(i: Int): Boolean {
        return type and i != 0
    }


    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun compareTo(o: VariableDeclaration): Int {
        return name.compareTo(o.name)
    }

    /*
    override fun toString(): String {
        return "$name : ${dataType?.name} := $init"
    }*/

    override fun clone(): VariableDeclaration {
        val vd = VariableDeclaration(name, type, typeDeclaration?.clone())
        vd.dataType = dataType
        vd.initValue = initValue
        return vd
    }


    class FlagCounter {
        private var internal = 1
        fun peek(): Int {
            return internal
        }

        fun get(): Int {
            val p = peek()
            internal = internal shl 1
            if (internal <= 0)
                throw IllegalStateException("Not enough flag bits left for variable declaration.")
            return p
        }
    }

    companion object {
        val FLAG_COUNTER = FlagCounter()
        val INPUT = FLAG_COUNTER.get()
        val OUTPUT = FLAG_COUNTER.get()
        val INOUT = FLAG_COUNTER.get() //INPUT | OUTPUT;
        val LOCAL = FLAG_COUNTER.get()
        val GLOBAL = FLAG_COUNTER.get()
        val CONSTANT = FLAG_COUNTER.get()
        val RETAIN = FLAG_COUNTER.get()
        val LOCATED = FLAG_COUNTER.get()
        val EXTERNAL = FLAG_COUNTER.get()
        val TEMP = FLAG_COUNTER.get()

        val WRITTEN_TO = FLAG_COUNTER.get()
        val READED = FLAG_COUNTER.get()
        val WRITE_BEFORE_READ = FLAG_COUNTER.get()
        val NOT_READ = FLAG_COUNTER.get()

        // Access specifiers
        val PUBLIC = FLAG_COUNTER.get()
        val INTERNAL = FLAG_COUNTER.get()
        val PROTECTED = FLAG_COUNTER.get()
        val PRIVATE = FLAG_COUNTER.get()
    }
}

interface HasRuleContext {
    val ruleContext: ParserRuleContext?

    val startPosition: Position
        get() = Position.start(ruleContext?.start)

    val endPosition: Position
        get() = Position.end(ruleContext?.stop)
}

data class Range(val start: IntegerLit, val stop: IntegerLit) : Cloneable {
    val startValue: Int
        get() = start.value.intValueExact()
    val stopValue: Int
        get() = stop.value.intValueExact()

    override fun clone() = Range(start.clone(), stop.clone())
    fun toIntRange(): IntRange = startValue..stopValue
}


private fun <T : Top> rctxHelper(target: T, source: T): T {
    target.ruleContext = source.ruleContext
    return target
}

enum class AccessSpecifier(val flag: Int) {
    PUBLIC(VariableDeclaration.PUBLIC), INTERNAL(VariableDeclaration.INTERNAL),
    PROTECTED(VariableDeclaration.PRIVATE), PRIVATE(VariableDeclaration.PUBLIC);
}

interface Classifier : HasMethods, HasInterfaces, Identifiable


//region SFC
data class ActionDeclaration(
        override var name: String = ANONYM,
        override var stBody: StatementList? = null,
        override var sfcBody: SFCImplementation? = null,
        override var ilBody: IlBody? = null,
        override var fbBody: FbdBody? = null)
    : Identifiable, HasBody, Top() {
    override fun clone(): ActionDeclaration {
        val a = ActionDeclaration()
        a.name = this.name
        a.stBody = stBody?.clone()
        a.sfcBody = sfcBody?.clone()
        return rctxHelper(a, this)
    }

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }
}

data class SFCActionQualifier(
        var qualifier: Qualifier = Qualifier.SET,
        var time: Expression = EMPTY_EXPRESSION
) {
    fun hasTime(): Boolean {
        return qualifier.hasTime
    }

    /*fun copy(): SFCActionQualifier {
        val q = SFCActionQualifier()
        q.qualifier = qualifier
        q.time = time!!.clone()
        return q
    }*/

    enum class Qualifier private constructor(val symbol: String, val hasTime: Boolean) {
        NON_STORED("N", false),
        OVERRIDING_RESET("R", false),
        SET("S", false),
        TIME_LIMITED("L", true),
        STORE_AND_DELAY("SD", true),
        STORE_AND_LIMITED("SL", true),
        STORE_DELAYED("D", true),           //could be renamed to TIME_DELAYED
        DELAYED_AND_STORED("DS", true),
        RAISING("P1", false),               //could be renamed to RISING
        FALLING("P0", false),
        PULSE("P", false),

        /** special case for code sys */
        WHILE("A", false)
    }

    companion object {
        fun fromName(qName: String): SFCActionQualifier? {
            val qualifier = Qualifier.entries.find { it.symbol == qName }
            if (qualifier != null) return SFCActionQualifier(qualifier)
            else return null
        }

        var RAISING = SFCActionQualifier(Qualifier.RAISING)
        var FALLING = SFCActionQualifier(Qualifier.FALLING)
        var NON_STORED = SFCActionQualifier(Qualifier.NON_STORED)
        var OVERRIDING_RESET = SFCActionQualifier(Qualifier.OVERRIDING_RESET)
        var SET = SFCActionQualifier(Qualifier.SET)
    }
}

data class SFCImplementation(
        val networks: MutableList<SFCNetwork> = ArrayList<SFCNetwork>()
        //weigl: actions now in PouExecutable
        // var actions: MutableList<ActionDeclaration> = ArrayList()
) : Top() {

    /**
     * {@inheritDoc}
     */
    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    override fun clone(): SFCImplementation {
        val sfc = SFCImplementation()
        cloneList(sfc.networks, networks)
        return rctxHelper(sfc, this)
    }
}


data class SFCStep(var name: String = ANONYM) : Top() {
    var isInitial: Boolean = false
    var events: MutableList<AssociatedAction> = ArrayList()
    var outgoing: MutableList<SFCTransition> = ArrayList()
    var incoming: MutableList<SFCTransition> = ArrayList()

    fun addAction(qualifier: SFCActionQualifier, text: String): AssociatedAction {
        val aa = AssociatedAction()
        aa.actionName = text
        aa.qualifier = qualifier
        events.add(aa)
        return aa
    }

    override fun clone(): SFCStep {
        val s = SFCStep()
        s.name = name
        s.isInitial = this.isInitial
        cloneList(s.events, events)
        s.outgoing = ArrayList(outgoing)
        s.incoming = ArrayList(incoming)
        return s
    }

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    data class AssociatedAction(
            var qualifier: SFCActionQualifier? = null,
            var actionName: String = ANONYM) : Cloneable {
        override fun clone(): AssociatedAction {
            val aa = AssociatedAction()
            aa.actionName = this.actionName
            aa.qualifier = this.qualifier!!.copy()
            return aa
        }
    }
}


private fun <T : Cloneable> cloneList(target: MutableCollection<in T>, source: Collection<out T>) {
    source.forEach { target += it.clone() as T }
}

private fun <K, V : Cloneable> cloneMap(target: MutableMap<K, V>, source: Map<K, V>) {
    source.forEach { k, v -> target.put(k, v.clone() as V) }
}

/*
private fun <E : Cloneable<*>> Collection<E>.clone(): MutableList<E> {
    val target = arrayListOf<E>()
    target.ensureCapacity(size)
    cloneList(target, this);
    return target
}
*/

class SFCTransition : Top() {
    var from: MutableSet<SFCStep> = HashSet()
    var to: MutableSet<SFCStep> = HashSet()
    var guard: Expression = BooleanLit.LTRUE
    var name: String = ANONYM
    var priority: Int = 0

    override fun clone(): SFCTransition {
        val t = SFCTransition()
        t.guard = this.guard.clone()
        t.name = this.name
        t.from = this.from.toMutableSet()
        t.to = this.to.toMutableSet()
        return t
    }

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    class PriorityComparison : Comparator<SFCTransition> {
        override fun compare(o1: SFCTransition, o2: SFCTransition): Int {
            return Integer.compare(o1.priority, o2.priority)
        }
    }
}

class SFCNetwork(var steps: MutableList<SFCStep> = ArrayList()) : Top() {
    val initialStep: SFCStep?
        get() = steps.stream().filter({ it.isInitial }).findFirst().orElse(null)

    override fun clone(): SFCNetwork {
        val sfcNetwork = SFCNetwork()
        cloneList(sfcNetwork.steps, steps)
        return sfcNetwork
    }

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    fun getStep(text: String): Optional<SFCStep> {
        return steps.stream().filter { s -> s.name.equals(text, ignoreCase = true) }.findAny()
    }
}

//endregion

