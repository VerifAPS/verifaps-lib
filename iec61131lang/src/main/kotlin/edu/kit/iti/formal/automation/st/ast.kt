package edu.kit.iti.formal.automation.st.ast

import com.google.common.base.Strings
import com.google.common.collect.ImmutableMap
import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.datatypes.values.ValueTransformation
import edu.kit.iti.formal.automation.exceptions.DataTypeNotResolvedException
import edu.kit.iti.formal.automation.exceptions.IECException
import edu.kit.iti.formal.automation.exceptions.TypeConformityException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.sfclang.split
import edu.kit.iti.formal.automation.st.*
import edu.kit.iti.formal.automation.st.Cloneable
import edu.kit.iti.formal.automation.st.util.Tuple
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.automation.visitors.Visitor
import org.antlr.v4.runtime.CommonToken
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import java.io.Serializable
import java.util.*
import java.util.function.Consumer
import kotlin.collections.ArrayList
import kotlin.reflect.full.memberProperties

sealed class Top : Visitable, edu.kit.iti.formal.automation.st.Cloneable<Top>,
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
                    .filter { it is Top }
                    .map { it as Top }
}

interface HasScope {
    var scope: Scope
}


//region Declaration and Toplevel
abstract class PouElement : Top(), Identifiable, Comparable<PouElement> {
    override fun compareTo(pouElement: PouElement): Int {
        return name.compareTo(pouElement.name)
    }
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

data class NamespaceDeclaration(
        var fqName: Array<String> = arrayOf(),
        val pous: PouElements = PouElements(),
        override var scope: Scope = Scope()) : HasScope, Top() {
    override fun <T> accept(visitor: Visitor<T>): T {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}

data class ConfigurationDeclaration(override var scope: Scope) : HasScope, PouElement() {
    override val name: String = "<configuration>"
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

class RefList<T : Identifiable>(private var impl: ArrayList<RefTo<T>> = arrayListOf()) : MutableList<RefTo<T>> by impl,
        Cloneable<RefList<T>> {
    fun add(element: String) = add(RefTo(element))

    override fun clone(): RefList<T> {
        val list = RefList<T>()
        forEach { list += it.clone() }
        return list
    }
}

data class FunctionBlockDeclaration(
        override var name: String = "<empty>",
        override var scope: Scope = Scope(),
        override var stBody: StatementList? = null,
        override var sfcBody: SFCImplementation? = null,
        var actions: LookupList<ActionDeclaration> = LookupListFactory.create(),
        var isFinal: Boolean = false,
        var isAbstract: Boolean = false,
        val interfaces: RefList<InterfaceDeclaration> = RefList(),
        val methods: MutableList<MethodDeclaration> = arrayListOf(),
        var parent: RefTo<FunctionBlockDeclaration> = RefTo()
) : PouExecutable(), Invocable {
    override val returnType = RefTo(AnyDt.VOID)

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
        override var name: String = "<empty>",
        override var scope: Scope = Scope(),
        var isFinal: Boolean = false,
        var isAbstract: Boolean = false,
        val interfaces: RefList<InterfaceDeclaration> = RefList(),
        val methods: MutableList<MethodDeclaration> = arrayListOf(),
        val parent: RefTo<ClassDeclaration> = RefTo<ClassDeclaration>()) : HasScope, PouElement() {

    override fun clone() = copy()
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class TypeDeclarations(private val declarations: MutableList<TypeDeclaration> = arrayListOf())
    : PouElement(), MutableList<TypeDeclaration> by declarations {

    override val name: String get() = "types"

    constructor(vararg stp: TypeDeclaration) : this() {
        declarations.addAll(Arrays.asList<TypeDeclaration>(*stp))
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    /*
    override fun clone(): TypeDeclarations {
        val td = TypeDeclarations()
        td.ruleContext = (ruleContext)
        forEach { t -> td.add(t.clone()) }
        return td
    }*/

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

interface HasBody : HasSfcBody, HasStBody
abstract class PouExecutable : PouElement(), HasScope, HasBody, Visitable


data class ProgramDeclaration(
        override var name: String = "<empty>",
        override var scope: Scope = Scope(),
        override var stBody: StatementList? = null,
        override var sfcBody: SFCImplementation? = null,
        var actions: LookupList<ActionDeclaration> = LookupList()
) : PouExecutable(), Identifiable {
    override fun clone() = copy()
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    fun addAction(act: ActionDeclaration) {
        this.actions.add(act)
    }
}

data class InterfaceDeclaration(
        override var name: String = "",
        var interfaces: RefList<InterfaceDeclaration> = RefList(),
        var methods: MutableList<MethodDeclaration> = arrayListOf()
) : PouElement(), Identifiable {

    /*fun clone(): InterfaceDeclaration {
        val i = InterfaceDeclaration()
        i.name = name
        methods.forEach { method -> i.methods.add(method.clone()) }
        interfaces.forEach { intf -> i.interfaces.add(intf.copy()) }
        return i
    }*/

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class FunctionDeclaration(
        override var name: String = "<empty>",
        override var scope: Scope = Scope(),
        override var returnType: RefTo<AnyDt> = RefTo(),
        override var stBody: StatementList? = StatementList()
) : PouExecutable(), Invocable {

    override var sfcBody: SFCImplementation?
        get() = null
        set(value) {
            throw IllegalStateException("Functions are not allowed to be an SFC. Internal would be required")
        }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    /*
    fun clone(): FunctionDeclaration {
        val fd = FunctionDeclaration()
        fd.name = this.name
        fd.returnType = returnType.copy()
        fd.stBody = stBody.clone()
        return fd
    }
    */
}

data class GlobalVariableListDeclaration(
        override var scope: Scope = Scope())
    : HasScope, PouElement() {

    override val name: String = "VAR_GLOBAL"
    override fun clone() = copy()
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class MethodDeclaration(
        override var name: String = "<empty>",
        override var returnType: RefTo<AnyDt> = RefTo(),
        override var scope: Scope = Scope(),
        var stBody: StatementList = StatementList(),
        var parent: Classifier? = null,
        var accessSpecifier: AccessSpecifier = AccessSpecifier.defaultAccessSpecifier(),
        var isFinal: Boolean = false,
        var isAbstract: Boolean = false,
        var isOverride: Boolean = false) : HasScope, Top(), Invocable, Identifiable {

    var returnTypeName: String?
        get() = if (returnType.identifier == null) "VOID" else returnType.identifier
        set(rt) {
            returnType.identifier = rt
        }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    /*
    override fun clone(): MethodDeclaration {
        val md = MethodDeclaration()
        md.accessSpecifier = accessSpecifier
        md.final_ = final_
        md.abstract_ = abstract_
        md.isOverride = isOverride
        md.scope = scope.copy()
        md.name = this.name
        md.returnType = returnType.copy()
        return md
    }*/
}
//endregion

//region Statements
object EMPTY_EXPRESSION : Expression() {
    override fun dataType(localScope: Scope): AnyDt = throw IllegalStateException()
    override fun clone(): Expression = EMPTY_EXPRESSION
    override fun <T> accept(visitor: Visitor<T>) = visitor.visit(this);
}

abstract class Statement : Top() {
    override fun clone(): Statement = super.clone() as Statement
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

data class AssignmentStatement(var location: Reference,
                               var expression: Expression = EMPTY_EXPRESSION,
                               var reference: Boolean = false) : Statement() {

    var isAssignmentAttempt: Boolean = false
        set(assignmentAttempt) {
            field = isAssignmentAttempt
        }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): AssignmentStatement {
        val a = AssignmentStatement(location, expression
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
        val cases: MutableList<Case> = arrayListOf(),
        var elseCase: StatementList? = StatementList())
    : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    fun addCase(cs: Case) {
        cases.add(cs)
    }

    /*
    override fun clone(): CaseStatement {
        val c = CaseStatement()
        c.ruleContext = ruleContext
        c.expression = expression!!.clone()
        cases.forEach { cs -> c.addCase(cs.clone()) }
        c.elseCase = Utils.copyNull<StatementList>(elseCase)
        return c
    }*/
}

data class Case(
        var conditions: MutableList<CaseCondition> = arrayListOf(),
        var statements: StatementList = StatementList()
) : Top() {

    fun addCondition(condition: CaseCondition) = conditions.add(condition)

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

/*        override fun clone(): Case {
            val c = Case()
            c.conditions = conditions.stream()
                    .map<CaseCondition>(Function<CaseCondition, CaseCondition> { it.copy() })
                    .collect<List<CaseCondition>, Any>(Collectors.toList())
            c.statements = statements.clone()
            return c
        }*/
}

class ExitStatement : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): Statement {
        val es = ExitStatement()
        es.ruleContext = ruleContext
        return es
    }

    companion object {

        var EXIT_STATMENT = ExitStatement()
    }
}

class ReturnStatement : Statement() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): ReturnStatement {
        val rt = ReturnStatement()
        rt.ruleContext = ruleContext
        return rt
    }
}

data class ForStatement(
        var variable: String = "<empty>",
        var start: Expression = EMPTY_EXPRESSION,
        var stop: Expression = EMPTY_EXPRESSION,
        var step: Expression? = EMPTY_EXPRESSION,
        var statements: StatementList = StatementList()) : Statement() {

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun clone(): Statement {
        val fs = ForStatement()
        fs.ruleContext = ruleContext
        fs.variable = variable
        if (start != null)
            fs.start = start!!.clone()
        if (stop != null)
            fs.stop = stop!!.clone()
        if (step != null)
            fs.step = step!!.clone()
        fs.statements = statements.clone()
        return fs
    }
}

data class CommentStatement(var comment: String) : Statement() {
    constructor(format: String, vararg args: Any) : this(String.format(format, *args)) {}

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun clone(): CommentStatement {
        return CommentStatement(comment)
    }

    companion object {
        fun box(s: String, vararg args: Any): Statement {
            var s = s
            val line = Strings.repeat("*", 79)
            s = (line + "\n *" + Strings.padEnd(String.format(s, *args) + "   ", 79, '*')
                    + "\n " + line)
            return CommentStatement(s)
        }

        fun single(fmt: String, vararg args: Any): Statement {
            return CommentStatement(fmt, *args)
        }
    }
}

data class GuardedStatement(
        var condition: Expression,
        var statements: StatementList = StatementList()) : Statement() {

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    /*override fun clone(): GuardedStatement {
        val gs = GuardedStatement()
        gs.ruleContext = gs.ruleContext
        gs.condition = condition.clone()
        gs.statements = statements.clone()
        return gs
    }*/
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

    /*override fun clone(): IfStatement {
        val `isType` = IfStatement()
        conditionalBranches.forEach { gs -> `isType`.addGuardedCommand(gs.clone()) }
        `isType`.elseBranch = this.elseBranch.clone()
        return `isType`
    }*/
}

data class InvocationStatement(var invocation: Invocation = Invocation()) : Statement() {
    val parameters = invocation.parameters

    var calleeName: String
        get() = invocation.calleeName
        set(calleeName) {
            invocation.calleeName = calleeName
        }

    val callee: SymbolicReference
        get() = invocation.callee

    val inputParameters: List<InvocationParameter>
        get() = invocation.inputParameters

    val outputParameters: List<InvocationParameter>
        get() = invocation.outputParameters

    constructor(fnName: String, vararg expr: Expression) : this(Invocation(fnName, *expr))

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    /*
    override fun clone(): InvocationStatement {
        val f = InvocationStatement()
        f.invocation=(invocation.copy())
        return f
    }*/
}
// endregion


//region Expressions
abstract class Expression : Top() {
    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    abstract fun dataType(localScope: Scope): AnyDt

    override fun clone() = super.clone() as Expression
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
        val c = operator.getPromotedType(a, b) ?: throw TypeConformityException(
                this, operator.expectedDataTypes, a, b
        )
        return operator.getPromotedType(a, b) ?: throw TypeConformityException(
                this, operator.expectedDataTypes, a, b
        )
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

    /*
    override fun clone(): UnaryExpression {
        val ue = UnaryExpression(operator, expression.clone())
        ue.ruleContext = ruleContext
        return ue
    }*/
}

data class SymbolicReference @JvmOverloads constructor(
        var identifier: String = "<empty>",
        var subscripts: ExpressionList? = null,
        var sub: SymbolicReference? = null,
        var dataType: AnyDt? = null) : Reference() {

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
            TODO()
            //return scope.getVariable(this).dataType.obj!!
        } catch (e: Exception) {
            throw VariableNotDefinedException(scope, this)
        }
    }

    /*
    override fun clone(): SymbolicReference {
        val sr = SymbolicReference()
        sr.ruleContext = ruleContext
        sr.identifier = identifier!!.copy()
        sr.subscripts = Utils.copyNull(subscripts)
        sr.sub = Utils.copyNull(sub)
        sr.derefCount = derefCount
        sr.dataType = dataType
        sr.effectiveDataType = effectiveDataType
        return sr
    }*/

    /*
    override fun toString(): String {
        return (getIdentifier()
                + Strings.repeat("^", derefCount)
                + (if (subscripts != null) subscripts!!.toString() else "")
                + if (sub == null) "" else "." + sub!!.toString())
    }*/
}
//endregion

data class Invocation(
        var callee: SymbolicReference = SymbolicReference(),
        val parameters: MutableList<InvocationParameter> = arrayListOf()
) : Expression() {
    private var invoked: RefTo<Invocable> = RefTo()

    val inputParameters: List<InvocationParameter>
        get() = parameters.filter { it.isInput }

    val outputParameters: List<InvocationParameter>
        get() = parameters.filter { it.isOutput }

    var calleeName: String
        get() = callee.toString()
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
        return if (invoked.isIdentified) {
            invoked.obj!!.returnType.obj!!
        } else {
            throw DataTypeNotResolvedException("Return type of function isType not set")
        }
    }

/*    override fun clone(): Invocation {
        val fc = Invocation(this)
        fc.ruleContext = ruleContext
        fc.callee = callee.clone()
        fc.parameters = parameters.map { it.copy() }
        return fc
    }
*/
}

data class InvocationParameter(
        var name: String? = "<empty>",
        var isOutput: Boolean = false,
        var expression: Expression = EMPTY_EXPRESSION
) : Top(), Comparable<InvocationParameter> {
    val isInput: Boolean
        get() = !isOutput

    constructor(expr: Expression) : this(expression = expr)

    /*
    fun clone(): InvocationParameter {
        return Parameter(this.name, isOutput, this.expression!!.clone())
    }*/

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
interface TypeDeclaration : HasRuleContext, Identifiable, Visitable {
    abstract override var name: String
    //var dataType: AnyDt
    @property:Deprecated("should be an type declaration")
    abstract var baseType: RefTo<AnyDt>
    abstract val initialization: Initialization?

    @Throws(IECException::class)
    fun getDataType(scope: Scope): AnyDt? =
            this.accept(TypeDeclarationToDataType(scope))

    fun setInit(initialization: Initialization?)
}

/**
 *
 */
data class SimpleTypeDeclaration(
        override var name: String = "<empty>",
        override var baseType: RefTo<AnyDt> = RefTo(),
        override var initialization: Initialization? = null
) : TypeDeclaration, Top() {

    override fun setInit(init: Initialization?) {
        initialization = init
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
/*    override fun clone(): SimpleTypeDeclaration {
        val std = SimpleTypeDeclaration()
        std.ruleContext = (ruleContext)
        std.baseType = baseType
        std.baseTypeName = baseTypeName
        std.typeName = typeName
        std.initialization = Utils.copyNull<T>(initialization)
        return std
    }*/
}

data class StructureTypeDeclaration(
        override var name: String = "<empty>",
        override var baseType: RefTo<AnyDt> = RefTo(),
        override var initialization: StructureInitialization? = null,
        var fields: VariableScope = LookupListFactory.create()
) : TypeDeclaration, Top() {
    override fun setInit(init: Initialization?) {
        initialization = init as StructureInitialization?
    }

    constructor(typeName: String, fields: List<VariableDeclaration>) : this() {
        name = typeName
        fields.forEach(Consumer<VariableDeclaration> { this.fields.add(it) })
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    /*
        override fun clone(): StructureTypeDeclaration {
            val t = StructureTypeDeclaration()
            t.ruleContext = ruleContext
            t.initialization = Utils.copyNull<StructureInitialization>(initialization)
            fields.forEach { k, v -> t.fields[k] = v.clone() }
            t.typeName = typeName
            t.baseType = baseType
            t.baseTypeName = baseTypeName
            return t
        }
    */
    fun addField(text: String, accept: TypeDeclaration): VariableDeclaration {
        val vd = VariableDeclaration(name = text, typeDeclaration = accept)
        fields.add(vd)
        return vd
    }
}

data class SubRangeTypeDeclaration(
        override var name: String = "<empty>",
        override var baseType: RefTo<AnyDt> = RefTo(),//TODO false, should be type declaration
        override var initialization: Literal? = null,//TODO Refine to integer literal
        var range: Range? = null)
    : TypeDeclaration, Top() {

    override fun setInit(init: Initialization?) {
        initialization = init as Literal?
    }

    /*override fun getDataType(scope: Scope): RangeType? {
        val start = Integer.valueOf(range!!.start.text)
        val stop = Integer.valueOf(range!!.stop.text)
        assert(start <= stop)
        val rt = RangeType(typeName, start, stop, super.getDataType(scope) as AnyInt)
        setDataType(rt)
        return rt
    }*/

    /*    override fun clone(): SubRangeTypeDeclaration {
            val t = SubRangeTypeDeclaration()
            t.range = Utils.copyNull(range)
            t.typeName = typeName
            t.baseType = baseType
            t.baseTypeName = baseTypeName
            t.initialization = Utils.copyNull<Literal>(initialization)
            return t
        }
    */
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

data class EnumerationTypeDeclaration(
        override var name: String = "<empty>",
        override var baseType: RefTo<AnyDt> = RefTo(),
        override var initialization: SymbolicReference? = null
) : TypeDeclaration, Top() {

    var allowedValues: MutableList<Token> = LinkedList()
    var values: MutableList<Int> = ArrayList()
    private var counter: Int = 0

    override fun setInit(init: Initialization?) {
        initialization = init as SymbolicReference?
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

    fun setInt(value: Literal) {
        val v = value.asValue() as VAnyInt
        values[values.size - 1] = v.value.toInt()
        counter = v.value.toInt() + 1
    }
}

data class ArrayTypeDeclaration(
        override var name: String = "<empty>",
        override var baseType: RefTo<AnyDt> = RefTo(),
        override var initialization: ArrayInitialization? = null,
        val ranges: MutableList<Range> = arrayListOf())
    : TypeDeclaration, Top() {
    private var type: ArrayType? = null

    override fun setInit(init: Initialization?) {
        initialization = init as ArrayInitialization?
    }


    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    /*
    override fun clone(): ArrayTypeDeclaration {
        val atd = ArrayTypeDeclaration()
        atd.ruleContext = ruleContext
        ranges.forEach { range -> atd.ranges.add(range.clone()) }
        atd.typeName = typeName
        atd.baseType = baseType
        atd.baseTypeName = baseTypeName
        atd.initialization = Utils.copyNull<ArrayInitialization>(initialization)
        return atd
    }
    */

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
        override var name: String = "<empty>",
        override var baseType: RefTo<AnyDt> = RefTo(),
        var size: Literal? = null,
        override var initialization: Literal? = null)
    : TypeDeclaration, Top() {

    override fun setInit(init: Initialization?) {
        initialization = init as Literal?
    }


/*    override fun getDataType(scope: Scope): AnyDt? {
        baseType = (IECString.STRING_16BIT)
        return baseType
    }

    override fun clone(): StringTypeDeclaration {
        val t = StringTypeDeclaration()
        t.initialization = initialization!!.clone()
        t.typeName = typeName
        t.baseType = baseType
        t.baseTypeName = baseTypeName
        t.size = size!!.clone()
        return t
    }
    */

    override fun <S> accept(visitor: Visitor<S>): S = visitor.visit(this)
}

class PointerTypeDeclaration(
        override var name: String = "<empty>",
        override var baseType: RefTo<AnyDt> = RefTo(),
        override var initialization: Literal? = null)
    : TypeDeclaration, Top() {

    override fun setInit(init: Initialization?) {
        initialization = init as Literal?
    }


    /*
    override fun getDataType(scope: Scope): PointerType? {
        val pt = PointerType(super.getDataType(scope))
        baseType = pt
        return pt
    }*/


    override fun <S> accept(visitor: Visitor<S>): S = visitor.visit(this)

    /*
    override fun clone(): PointerTypeDeclaration {
        return PointerTypeDeclaration(baseTypeName)
    }*/
}

class ReferenceTypeDeclaration(
        override var name: String = "<empty>",
        var refTo: SimpleTypeDeclaration = SimpleTypeDeclaration(),
        override var baseType: RefTo<AnyDt> = refTo.baseType)
    : TypeDeclaration, Top() {
    override var initialization: Literal? = null

    override fun setInit(init: Initialization?) {
        initialization = init as Literal?
    }


    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    /* override fun clone(): ReferenceTypeDeclaration {
        val rs = ReferenceTypeDeclaration()
        rs.refTo = refTo
        rs.baseType = baseType
        return rs
    }*/
}
//endregion


//region Initialization
abstract class Initialization : Expression() {
    override fun clone() = super.clone() as Initialization
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

    /*
    override fun clone(): StructureInitialization {
        val st = StructureInitialization()
        st.structureName = structureName
        st.initValues = HashMap(initValues)
        return st
    }*/
}

class IdentifierInitializer(var enumType: EnumerateType? = null,
                            var value: String? = null) : Initialization() {

    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    override fun dataType(localScope: Scope): AnyDt {
        return enumType!!
    }

    /*
    override fun clone(): IdentifierInitializer {
        return IdentifierInitializer(value).setEnumType(enumType)
    }
    */

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
        /*
        override fun clone(): Range {
            val r = Range(this.start!!.clone(), Utils.copyNull<Literal>(this.stop))
            r.ruleContext = (ruleContext)
            return r
        }
    */
    }

    data class IntegerCondition(var value: Literal) : CaseCondition() {
        override fun <T> accept(visitor: Visitor<T>): T {
            return visitor.visit(this)
        }

        /*override fun clone(): IntegerCondition {
            return IntegerCondition(this.value!!.clone())
        }*/
    }

    data class Enumeration(var start: Literal, var stop: Literal? = null) : CaseCondition() {
        constructor(start: Literal) : this(start, start)

        override fun <T> accept(visitor: Visitor<T>): T {
            return visitor.visit(this)
        }

        /*
        override fun clone(): Enumeration {
            val e = Enumeration(start.clone(), if (stop != null) stop!!.clone() else null)
            e.ruleContext = (ruleContext)
            return e
        }*/
    }
}

class Deref(private val reference: Reference) : Reference() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun dataType(localScope: Scope): AnyDt {
        return reference.dataType(localScope)//TODO
    }

/*    override fun clone(): Deref {
        return Deref(reference.clone())
    }*/
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

interface Invocable : Identifiable {
    val returnType: RefTo<out AnyDt>
}

class Literal : Initialization {
    val dataType = RefTo<AnyDt>()
    var dataTypeExplicit: Boolean = false
    var token: Token? = null
    // for integers only
    var signed: Boolean = false


    val textValue: String?
        get() {
            val s = split(text)
            return s.value
        }

    val dataTypeName: String?
        get() = dataType.identifier

    val text: String
        get() = (if (signed) "-" else "") + token!!.text

    constructor(dataTypeName: String?, symbol: Token) {
        token = symbol
        dataType.identifier = dataTypeName
        assert(dataTypeName != null)
    }


    constructor(dataTypeName: String?, symbol: String) {
        token = CommonToken(-1, symbol)
        dataType.identifier = dataTypeName
        assert(dataTypeName != null)
    }

    constructor(dataType: AnyDt, symbol: String) {
        token = CommonToken(-1, symbol)
        this.dataType.obj = dataType
    }

    constructor(dataType: AnyDt, symbol: Token) {
        token = symbol
        this.dataType.obj = dataType
    }

    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    override fun dataType(localScope: Scope): AnyDt {
        return dataType.obj!!
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    fun asValue(): Value<*, *>? = asValue(ValueTransformation(this))

    private fun asValue(transformer: DataTypeVisitor<Value<*, *>>): Value<*, *> =
            if (dataType.obj == null)
                throw IllegalStateException(
                        "no identified data type. given data type name " + dataType.identifier!!)
            else
                dataType.obj!!.accept(transformer)!!

/*
override fun clone(): Literal {
    val l = Literal(dataTypeName, getToken())
    l.dataTypeExplicit = dataTypeExplicit
    l.signed = signed
    l.dataType.setIdentifier(dataType.identifier)
    l.dataType.setIdentifiedObject(dataType.obj)
    return l
}*/

    companion object {
        val FALSE = Literal(AnyBit.BOOL, "FALSE")
        val TRUE = Literal(AnyBit.BOOL, "TRUE")

        fun integer(token: Token, signed: Boolean): Literal {
            val l = Literal(ANY_INT, token)
            val s = split(token.text)
            if (s.prefix != null) {
                l.dataTypeExplicit = true
                l.dataType.obj = DataTypes.getDataType(s.prefix)
            }
            l.signed = signed
            return l
        }

        fun enumerate(token: Token): Literal {
            val dataTypeName = token.text.split("[.#]".toRegex()).dropLastWhile({ it.isEmpty() }).toTypedArray()[0]
            return Literal(dataTypeName, token)
        }

        fun bool(symbol: Token): Literal {
            assert("TRUE".equals(symbol.text, ignoreCase = true) || "FALSE".equals(symbol.text, ignoreCase = true))
            return Literal(AnyBit.BOOL, symbol)
        }

        fun word(symbol: Token): Literal {
            val s = symbol.text
            val first = split(s)

            if ("TRUE".equals(first.value, ignoreCase = true))
                return bool(symbol)
            if ("FALSE".equals(first.value, ignoreCase = true))
                return bool(symbol)


            var dataType: AnyBit? = null
            if (first.prefix != null) {
                dataType = AnyBit.DATATYPES
                        .stream()
                        .filter { a -> a.name.equals(first.prefix, ignoreCase = true) }
                        .findAny()
                        .get()

            }
            return Literal(dataType!!, symbol)
        }

        fun real(symbol: Token): Literal {
            return Literal(AnyReal.REAL, symbol)
        }

        fun string(symbol: Token, b: Boolean): Literal {
            return Literal(if (b) IECString.WSTRING else IECString.STRING, symbol)

        }


        fun time(text: Token): Literal {
            return Literal(TimeType.TIME_TYPE, text)
        }

        fun timeOfDay(text: Token): Literal {
            return Literal(AnyDate.TIME_OF_DAY, text)

        }

        fun date(symbol: Token): Literal {
            return Literal(AnyDate.DATE, symbol)

        }

        fun dateAndTime(symbol: Token): Literal {
            return Literal(AnyDate.DATE_AND_TIME, symbol)
        }

        fun integer(`val`: Int): Literal {
            return integer(CommonToken(-1, "" + Math.abs(`val`)), `val` < 0)
        }

        fun ref_null(symbol: Token): Literal {
            return Literal(ReferenceDt.ANY_REF, symbol)
        }
    }
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

    /*
    override fun clone(): Location {
        val l = Location(
                path.stream().map<Reference>(Function<Reference, Reference> { it.copy() })
                        .collect<List<Reference>, Any>(Collectors.toList()))
        l.ruleContext = ruleContext
        return l
    }*/
}


//region Helpers
class StatementList(private var list: MutableList<Statement> = arrayListOf())
    : Statement(), MutableList<Statement> by list {

    constructor(vararg then: Statement) : this() {
        list = ArrayList(Arrays.asList(*then))
    }

    constructor(statements: StatementList) : this() {
        addAll(statements)
    }

    constructor(ts: Collection<Statement>) : this() {
        list = ArrayList(ts)
    }

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    fun comment(format: String, vararg args: Any) {
        add(CommentStatement(format, *args))
    }

    override fun clone(): StatementList = StatementList(map { it.clone() })
}

data class ExpressionList(private val expressions: MutableList<Expression> = arrayListOf())
//TODO check for expression
    : Expression(), MutableList<Expression> by expressions {

    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)

    override fun dataType(localScope: Scope): AnyDt {
        throw IllegalStateException("not implemented")
    }

    override fun clone(): ExpressionList {
        val el = ExpressionList()
        forEach { e -> el.add(e.clone()) }
        return el
    }
}

data class Position(
        val lineNumber: Int = -1,
        val charInLine: Int = -1,
        val offset: Int = -1) : edu.kit.iti.formal.automation.st.Cloneable<Position> {

    constructor(token: Token) : this(token.line, token.charPositionInLine, token.startIndex) {}

    /*
    public override fun clone(): Position {
        return Position(lineNumber, charInLine, offset)
    }*/

    override fun toString(): String {
        return "@$lineNumber:$charInLine"
    }
}
//endregion 


abstract class Reference : Initialization() {
    //abstract override fun clone(): Reference
}

class VariableBuilder(val scope: VariableScope) {
    private val stack = Stack<Int>()
    private var initialization: Initialization? = null
    private var identifiers: List<String>? = null
    private var type: TypeDeclaration? = null
    private val pEnd: Position? = null
    private val pStart: Position? = null

    //region Handling of special flags (like constant, input or global)


    fun clear(): VariableBuilder {
        identifiers = null
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
        val td = SimpleTypeDeclaration()
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


    fun create(): VariableBuilder {
        for (id in identifiers!!) {
            val vd = VariableDeclaration(id, peek(), type!!)
            this.scope.add(vd)
        }
        return this
    }


    fun close(): VariableBuilder {
        return create().clear()
    }


    fun identifiers(ast: List<String>): VariableBuilder {
        identifiers = ast
        return this
    }


    fun identifiers(vararg functionName: String): VariableBuilder {
        return identifiers(Arrays.asList(*functionName))
    }
}

data class VariableDeclaration(
        override var name: String = "<empty>",
        var type: Int = 0,
        var typeDeclaration: TypeDeclaration? = null
) : Top(), Comparable<VariableDeclaration>, Identifiable {
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
    }

    fun isType(i: Int): Boolean {
        return type and i != 0
    }


    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
    override fun compareTo(o: VariableDeclaration): Int {
        return name.compareTo(o.name)
    }

    override fun toString(): String {
        return "$name : ${dataType?.name} := $init"
    }

    /*    override fun clone(): VariableDeclaration {
            val vd = VariableDeclaration(name, type, typeDeclaration!!)
            if (dataType != null)
                vd.dataType = dataType
            vd.init = init
            vd.parent = vd.parent
            return vd
        }
    */

    override fun clone() = super.clone() as VariableDeclaration

    class FlagCounter {
        private var internal = 1
        fun peek(): Int {
            return internal
        }

        fun get(): Int {
            val p = peek()
            internal = internal shl 1
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

        val ACCESS_SPECIFIER_DICT: Map<AccessSpecifier, Int> = ImmutableMap.of(
                AccessSpecifier.PUBLIC, PUBLIC,
                AccessSpecifier.INTERNAL, INTERNAL,
                AccessSpecifier.PROTECTED, PROTECTED,
                AccessSpecifier.PRIVATE, PRIVATE)
    }
}

interface HasRuleContext {
    val ruleContext: ParserRuleContext?

    val startPosition: Position
        get() = Position(ruleContext!!.start)

    val endPosition: Position
        get() = Position(ruleContext!!.stop)
}

data class Range(val start: Literal, val stop: Literal) : Cloneable<Range> {

    val startValue: Int
        get() = Integer.valueOf(start.text)

    val stopValue: Int
        get() = Integer.valueOf(stop.text)

    constructor(start: Int, stop: Int) : this(Literal.integer(start), Literal.integer(stop)) {}

    constructor(p: Tuple<Int, Int>) : this(p.a, p.b) {}

    /*
    override fun clone(): Range {
        return Range(start.clone(), stop.clone())
    }*/
}

enum class AccessSpecifier(val flag: Int) {
    PUBLIC(VariableDeclaration.PUBLIC), INTERNAL(VariableDeclaration.INTERNAL),
    PROTECTED(VariableDeclaration.PRIVATE), PRIVATE(VariableDeclaration.PUBLIC);

    companion object {
        fun defaultAccessSpecifier() = PROTECTED
    }
}

interface Classifier {
    val interfaces: List<RefTo<InterfaceDeclaration>>
    val methods: List<MethodDeclaration>
}


//region SFC
data class ActionDeclaration(
        override var name: String = "<empty>",
        var stBody: StatementList? = null,
        var sfcBody: SFCImplementation? = null
) : Top(), Invocable {
    override val returnType: RefTo<out AnyDt> = RefTo(AnyDt.VOID)

    /*fun clone(): ActionDeclaration {
        val a = ActionDeclaration()
        a.name = this.name
        if (stBody != null)
            a.stBody = stBody!!.clone()
        if (sfcBody != null)
            a.sfcBody = sfcBody!!.clone()
        return a
    }*/

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }
}

data class SFCActionQualifier(
        var qualifier: Qualifier = Qualifier.SET,
        var time: Expression = EMPTY_EXPRESSION
) {
    fun hasTime(): Boolean {
        return qualifier!!.hasTime
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
        STORE_DELAYED("D", true),
        DELAYED_AND_STORED("DS", true),
        RAISING("P1 ", false),
        FALLING("P0", false)
    }

    companion object {
        fun fromName(qName: String): SFCActionQualifier? {
            val qualifier = Qualifier.values().find { it.symbol == qName }
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
        val networks: MutableList<SFCNetwork> = ArrayList<SFCNetwork>(),
        var actions: MutableList<ActionDeclaration> = ArrayList()
) : Top() {

    fun getAction(name: String): ActionDeclaration? {
        return this.actions.stream().filter { a: ActionDeclaration -> a.name == name }.findFirst().orElse(null)
    }

    /**
     * {@inheritDoc}
     */
    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    /*
    fun clone(): SFCImplementation {
        val sfc = SFCImplementation()
        networks.forEach { a -> sfc.networks.add(a.clone()) }
        throw IllegalStateException("not implemented yet!")
    }*/
}

data class SFCStep(var name: String = "<empty>") : Top() {
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

    /*fun clone(): SFCStep {
        val s = SFCStep()
        s.name = name
        s.isInitial = this.isInitial
        s.events = events.stream()
                .map { e -> e.copy() }
                .collect<List<AssociatedAction>, Any>(Collectors.toList())
        s.outgoing = ArrayList(outgoing)
        s.incoming = ArrayList(incoming)
        return s
    }*/

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    data class AssociatedAction(
            var qualifier: SFCActionQualifier? = null,
            var actionName: String = "<empty>") {
        /*fun copy(): AssociatedAction {
            val aa = AssociatedAction()
            aa.actionName = this.actionName
            aa.qualifier = this.qualifier!!.copy()
            return aa
        }*/
    }
}

class SFCTransition : Top() {
    var from: Set<SFCStep>? = null
        set(from) {
            field = this.from
        }
    var to: Set<SFCStep>? = null
        set(to) {
            field = this.to
        }
    var guard: Expression? = null
        set(guard) {
            field = this.guard
        }
    var name: String? = null
        set(name) {
            field = this.name
        }
    var priority: Int = 0
        set(priority) {
            field = this.priority
        }

    /*fun clone(): Top<*> {
        val t = SFCTransition()
        t.name = this.name
        t.from = this.from //TODO deep clone
        t.to = this.to // TODO deep clone
        return t
    }*/

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

    /*
    fun clone(): SFCNetwork {
        val sfcNetwork = SFCNetwork()
        sfcNetwork.steps = steps.stream().map { n -> n.clone() }.collect<List<SFCStep>, Any>(Collectors.toList())
        return sfcNetwork
    }*/

    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    fun getStep(text: String): Optional<SFCStep> {
        return steps.stream().filter { s -> s.name.equals(text, ignoreCase = true) }.findAny()
    }
}

//endregion