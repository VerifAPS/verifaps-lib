package edu.kit.iti.formal.automation.st

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.IECString
import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.operators.Operator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto
import java.util.*

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
class StructuredTextPrinter
@JvmOverloads constructor(var sb: CodeWriter = CodeWriter()) : AstVisitor<Unit>() {
    private val literals: StringLiterals = SL_ST
    var bodyPrinting = BodyPrinting.ST
    var isPrintComments: Boolean = false

    val string: String
        get() = sb.toString()


    override fun defaultVisit(visitable: Any) {
        throw IllegalArgumentException("not implemented: " + visitable!!::class.java)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {
        sb.printf("ARRAY[")
        arrayTypeDeclaration.ranges.forEachIndexed { i, it ->
            it.start.accept(this)
            sb.printf("..")
            it.stop.accept(this)
            if (i < arrayTypeDeclaration.ranges.size - 1)
                sb.printf(", ")
        }
        sb.printf("] OF ")
        sb.printf(arrayTypeDeclaration.baseType.identifier!!)
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration) {
        sb.printf("STRING")
    }

    override fun visit(elements: PouElements) {
        elements.forEach { it.accept(this) }
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(exitStatement: ExitStatement) {
        sb.printf(literals.exit()).printf(literals.statement_separator())

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(integerCondition: CaseCondition.IntegerCondition) {
        sb.appendIdent()
        integerCondition.value!!.accept(this)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumeration: CaseCondition.Enumeration) {
        if (enumeration.start == enumeration.stop) {
            enumeration.start.accept(this)
        } else {
            enumeration.start.accept(this)
            sb.printf("..")
            enumeration.stop!!.accept(this)
        }


    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression) {
        sb.append('(')
        binaryExpression.leftExpr!!.accept(this)
        sb.printf(" ").printf(literals.operator(binaryExpression.operator)).printf(" ")
        binaryExpression.rightExpr!!.accept(this)
        sb.append(')')

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(assignStatement: AssignmentStatement) {
        sb.nl()
        assignStatement.location.accept(this)
        if (assignStatement.isAssignmentAttempt)
            sb.printf(literals.assignmentAttempt())
        else
            sb.printf(literals.assign())
        assignStatement.expression.accept(this)
        sb.printf(";")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(configurationDeclaration: ConfigurationDeclaration) {

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        sb.nl().printf(enumerationTypeDeclaration.name).printf(" : ")
        enumerationTypeDeclaration.allowedValues.joinTo(sb, ", ", "(", ");")
    }

    override fun visit(init: IdentifierInitializer) {
        sb.printf(init.value!!)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement) {
        sb.nl()
        sb.printf("REPEAT").increaseIndent()
        repeatStatement.statements.accept(this)

        sb.decreaseIndent().nl().printf("UNTIL ")
        repeatStatement.condition.accept(this)
        sb.printf("END_REPEAT")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement) {
        sb.nl()
        sb.printf("WHILE ")
        whileStatement.condition.accept(this)
        sb.printf(" DO ").increaseIndent()
        whileStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("END_WHILE")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression) {
        sb.printf(literals.operator(unaryExpression.operator)!!).printf(" ")
        unaryExpression.expression.accept(this)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations) {

        if (typeDeclarations.size > 0) {
            sb.printf("TYPE ").increaseIndent()
            for (decl in typeDeclarations) {
                decl.accept(this)
            }
            sb.decreaseIndent().nl().printf("END_TYPE").nl().nl()
        }

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(caseStatement: CaseStatement) {

        sb.nl().printf("CASE ")
        caseStatement.expression!!.accept(this)
        sb.printf(" OF ").increaseIndent()

        for (c in caseStatement.cases) {
            c.accept(this)
            sb.nl()
        }

        if (caseStatement.elseCase!!.size > 0) {
            sb.nl().printf("ELSE ")
            caseStatement.elseCase!!.accept(this)
        }

        sb.nl().decreaseIndent().appendIdent().printf("END_CASE;")

    }

    override fun visit(symbolicReference: SymbolicReference) {
        sb.printf(symbolicReference.identifier)

        for (i in 0 until symbolicReference.derefCount)
            sb.printf("^")

        if (symbolicReference.subscripts != null && !symbolicReference.subscripts!!.isEmpty()) {
            symbolicReference.subscripts!!.joinInto(sb, ", ", "[", "]") { it.accept(this) }
        }

        if (symbolicReference.sub != null) {
            sb.printf(".")
            symbolicReference.sub!!.accept(this)
        }


    }

    /**
     * {@inheritDoc}
     */
    override fun visit(statements: StatementList) {
        for (stmt in statements) {
            stmt.accept(this)
        }

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(pd: ProgramDeclaration) {
        printComment(pd.comment)
        sb.printf("PROGRAM ").printf(pd.name).increaseIndent()
        pd.scope.accept(this)

        sb.nl()

        if (!pd.actions.isEmpty()) {
            pd.actions.forEach { v -> v.accept(this) }
            sb.nl()
        }

        printBody(pd.stBody, pd.sfcBody)

        sb.decreaseIndent().nl().printf("END_PROGRAM").nl()

    }


    /*
     * TODO to new ast visitor
     *
     * @Override public Object accept(CaseExpression caseExpression) {
     * sb.printf("CASES(").increaseIndent(); for (CaseExpression.Case cas :
     * caseExpression.getCases()) { cas.getCondition().accept(this); sb.printf(
     * " -> "); cas.getExpression().accept(this); sb.printf(";").nl(); }
     * sb.printf("ELSE -> "); caseExpression.getElseExpression().accept(this);
     * sb.printf(")").decreaseIndent(); ; }
     */

    /**
     * {@inheritDoc}
     */
    override fun visit(expressions: ExpressionList) {
        expressions.joinInto(sb) { it.accept(this) }
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(invocation: Invocation) {
        invocation.callee.accept(this)
        visitInvocationParameter(invocation.parameters)
    }

    private fun visitInvocationParameter(parameters: MutableList<InvocationParameter>) {
        parameters.joinInto(sb, ", ", "(", ")") {
            if (it.name != null) {
                sb.printf(it.name!!)
                if (it.isOutput)
                    sb.printf(" => ")
                else
                    sb.printf(" := ")
            }
            it.expression.accept(this)
        }
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement) {
        sb.nl()
        sb.printf("FOR ").printf(forStatement.variable)
        sb.printf(" := ")
        forStatement.start!!.accept(this)
        sb.printf(" TO ")
        forStatement.stop!!.accept(this)
        sb.printf(" DO ").increaseIndent()
        forStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("END_FOR")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        printComment(functionBlockDeclaration.comment)
        sb.printf("FUNCTION_BLOCK ")
        if (functionBlockDeclaration.isFinal)
            sb.printf("FINAL ")
        if (functionBlockDeclaration.isAbstract)
            sb.printf("ABSTRACT ")

        sb.printf(functionBlockDeclaration.name)

        if (functionBlockDeclaration.parent.identifier != null) {
            sb.printf(" EXTENDS ").printf(functionBlockDeclaration.parent.identifier!!)
        }

        if (functionBlockDeclaration.interfaces.isNotEmpty()) {
            val interf = functionBlockDeclaration.interfaces
                    .map { it.identifier!! }
                    .joinToString(", ")
            sb.printf(" IMPLEMENTS ").printf(interf);
        }
        sb.increaseIndent().nl()
        functionBlockDeclaration.scope.accept(this)
        sb.nl()

        if (functionBlockDeclaration.methods.isNotEmpty()) {
            functionBlockDeclaration.methods.forEach { it.accept(this) }
            sb.nl()
        }

        if (!functionBlockDeclaration.actions.isEmpty()) {
            functionBlockDeclaration.actions.forEach { v -> v.accept(this) }
        }

        printBody(functionBlockDeclaration.stBody, functionBlockDeclaration.sfcBody)

        sb.decreaseIndent().nl().printf("END_FUNCTION_BLOCK").nl().nl()

    }

    private fun printComment(comment: String) {
        if (comment.isNotBlank()) {
            sb.printf(literals.comment_open())
            sb.printf(comment)
            sb.printf(literals.comment_close()+"\n")
        }
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        sb.printf("INTERFACE ").printf(interfaceDeclaration.name)

        val extendsInterfaces = interfaceDeclaration.interfaces.map { it.identifier }
        if (!extendsInterfaces.isEmpty())
            sb.printf(" EXTENDS ").print(extendsInterfaces)

        sb.increaseIndent().nl()

        //interfaceDeclaration.scope.accept(this)

        interfaceDeclaration.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().printf("END_INTERFACE").nl().nl()

    }

    override fun visit(clazz: ClassDeclaration) {
        printComment(clazz.comment)
        sb.printf("CLASS ")

        if (clazz.isFinal)
            sb.printf("FINAL ")
        if (clazz.isAbstract)
            sb.printf("ABSTRACT ")

        sb.printf(clazz.name)

        val parent = clazz.parent.identifier
        if (parent != null)
            sb.printf(" EXTENDS ").printf(parent)

        val interfaces = clazz.interfaces.map { it.identifier }
        if (!interfaces.isEmpty())
            sb.printf(" IMPLEMENTS ").printf(interfaces.joinToString(","))

        sb.increaseIndent().nl()

        clazz.scope.accept(this)

        clazz.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().printf("END_CLASS").nl().nl()

    }

    override fun visit(method: MethodDeclaration) {
        sb.printf("METHOD ")

        if (method.isFinal)
            sb.printf("FINAL ")
        if (method.isAbstract)
            sb.printf("ABSTRACT ")
        if (method.isOverride)
            sb.printf("OVERRIDE ")

        sb.printf(method.accessSpecifier.toString() + " ")

        sb.printf(method.name)

        val returnType = method.returnTypeName
        if (!returnType!!.isEmpty())
            sb.printf(" : $returnType")

        sb.increaseIndent().nl()

        method.scope.accept(this)

        method.stBody.accept(this)

        sb.decreaseIndent().nl().printf("END_METHOD").nl().nl()

    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        printComment(functionDeclaration.comment)
        sb.printf("FUNCTION ").printf(functionDeclaration.name)

        val returnType = functionDeclaration.returnType.identifier
        if (!(returnType == null || returnType.isEmpty()))
            sb.printf(" : $returnType")

        sb.increaseIndent().nl()

        functionDeclaration.scope.accept(this)

        functionDeclaration.stBody?.accept(this)

        sb.decreaseIndent().nl().printf("END_FUNCTION").nl().nl()

    }

    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration) {
        globalVariableListDeclaration.scope.accept(this)
        sb.nl()

    }

    override fun visit(referenceSpecification: ReferenceTypeDeclaration) {
        sb.printf("REF_TO ")
        referenceSpecification.refTo?.accept(this)
    }

    override fun visit(referenceValue: ReferenceValue) {
        sb.printf("REF(")
        referenceValue.referenceTo.accept(this)
        sb.printf(")")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(returnStatement: ReturnStatement) {
        sb.nl().printf("RETURN;")
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(ifStatement: IfStatement) {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            sb.nl()

            if (i == 0)
                sb.printf("IF ")
            else
                sb.printf("ELSEIF ")

            ifStatement.conditionalBranches[i].condition.accept(this)

            sb.printf(" THEN").increaseIndent()
            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.decreaseIndent()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.nl().printf("ELSE").increaseIndent()
            ifStatement.elseBranch.accept(this)
            sb.decreaseIndent()
        }
        sb.nl().printf("END_IF")

    }

    override fun visit(ad: ActionDeclaration) {
        sb.nl().printf("ACTION ").printf(ad.name).increaseIndent()
        printBody(ad.stBody, ad.sfcBody)
        sb.decreaseIndent().nl().printf("END_ACTION")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(fbc: InvocationStatement) {
        sb.nl()
        fbc.callee.accept(this)
        visitInvocationParameter(fbc.parameters)
        sb.printf(";")
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: Case) {
        sb.nl()
        aCase.conditions.joinInto(sb) { it.accept(this) }
        sb.printf(":")
        sb.block() {
            aCase.statements.accept(this@StructuredTextPrinter)
        }
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        sb.printf(simpleTypeDeclaration.baseType.identifier!!)
        /*if (simpleTypeDeclaration.initialization != null) {
            sb.printf(" := ")
            simpleTypeDeclaration.initialization!!.accept(this)
        }*/
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        sb.printf(structureTypeDeclaration.name)
        sb.printf(": STRUCT").nl().increaseIndent()
        structureTypeDeclaration.fields.forEach { it ->
            sb.nl()
            it.accept(this)
        }
        sb.decreaseIndent().printf("END_STRUCT;").nl()

    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration) {
        sb.printf(subRangeTypeDeclaration.name)
        sb.printf(": ").printf(subRangeTypeDeclaration.baseType.identifier!!)
        sb.printf("(")
        subRangeTypeDeclaration.range!!.start.accept(this)
        sb.printf(" .. ")
        subRangeTypeDeclaration.range!!.stop.accept(this)
        sb.printf(")")
        /*if (subRangeTypeDeclaration.initialization != null) {
            sb.printf(" := ")
            subRangeTypeDeclaration.initialization!!.accept(this)
        }*/
        sb.printf(";")

    }

    val variableDeclarationUseDataType = false
    private fun variableDataType(vd: VariableDeclaration) {
        val dt = vd.dataType
        if (variableDeclarationUseDataType && dt != null) {
            variableDataType(dt)
        } else {
            vd.typeDeclaration?.accept(this)
        }
    }

    fun variableDataType(dt: AnyDt): Unit {
        sb.printf(dt.reprDecl())
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(commentStatement: CommentStatement) {
        if (isPrintComments) {
            sb.nl()
            sb.printf(literals.comment_open())
            sb.printf(commentStatement.comment)
            sb.printf(literals.comment_close())
        }
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(literal: Literal) {
        fun print(prefix: Any?, suffix: Any) =
                (if (prefix != null) "$prefix#" else "") + suffix

        sb.printf(when (literal) {
            is IntegerLit -> print(literal.dataType.obj?.name, literal.value.abs())
            is RealLit -> print(literal.dataType.obj?.name, literal.value.abs())
            is EnumLit -> print(literal.dataType.obj?.name, literal.value)
            is ToDLit -> {
                val (h, m, s, ms) = literal.value
                print(literal.dataType().name, "$h:$m:$s.$ms")
            }
            is DateLit -> {
                val (y, m, d) = literal.value
                print(literal.dataType().name, "$y-$m-$d")
            }
            is DateAndTimeLit -> {
                val (y, mo, d) = literal.value.date
                val (h, m, s, ms) = literal.value.tod
                print(literal.dataType().name, "$y-$m-$d-$h:$m:$s.$ms")
            }
            is StringLit -> {
                if (literal.dataType() is IECString.WSTRING) "\"${literal.value}\""
                else "'${literal.value}'"
            }
            is NullLit -> "null"
            is TimeLit -> {
                print(literal.dataType().name, "${literal.value.milliseconds}ms")
            }
            is BooleanLit -> literal.value.toString().toUpperCase()
            is BitLit -> {
                print(literal.dataType.obj?.name, "2#" + literal.value.toString(2))
            }
            is UnindentifiedLit -> literal.value
        })
    }

    override fun visit(initializations: ArrayInitialization) {
        initializations.initValues.joinInto(sb, ", ", "[", "]") {
            it.accept(this)
        }
    }

    override fun visit(localScope: Scope) {
        val variables = VariableScope(localScope.variables)
        variables.groupBy { it.type }
                .forEach { type, v ->
                    val vars = v.toMutableList()
                    vars.sortWith(compareBy { it.name })

                    //By { a, b -> a.compareTo(b) }
                    sb.nl().printf("VAR")

                    if (VariableDeclaration.INPUT and type >= VariableDeclaration.INOUT) {
                        sb.printf("_INOUT")
                    } else {
                        if (VariableDeclaration.INPUT and type != 0)
                            sb.printf("_INPUT")
                        if (VariableDeclaration.OUTPUT and type != 0)
                            sb.printf("_OUTPUT")
                        if (VariableDeclaration.EXTERNAL and type != 0)
                            sb.printf("_EXTERNAL")
                        if (VariableDeclaration.GLOBAL and type != 0)
                            sb.printf("_GLOBAL")
                        if (VariableDeclaration.TEMP and type != 0)
                            sb.printf("_TEMP")
                    }
                    sb.printf(" ")
                    if (VariableDeclaration.CONSTANT and type != 0)
                        sb.printf("CONSTANT ")
                    if (VariableDeclaration.RETAIN and type != 0)
                        sb.printf("RETAIN ")
                    sb.printf(" ")
                    //sb.printf(type)

                    sb.increaseIndent()
                    for (vd in vars) {
                        sb.nl()
                        sb.printf(vd.name).printf(" : ")
                        variableDataType(vd)
                        if (vd.init != null) {
                            sb.printf(" := ")
                            vd.init!!.accept(this)
                        } else if (vd.initValue != null) {
                            sb.printf(" := ")
                            val (dt, v) = vd.initValue as Value<*, *>
                            sb.printf(dt.repr(v))
                        }
                        sb.printf(";")
                    }
                    sb.decreaseIndent().nl().printf("END_VAR")
                    sb.nl()
                }
    }

    override fun visit(structureInitialization: StructureInitialization) {
        structureInitialization.initValues.joinInto(sb, ", ", "(", ")")
        { t, v ->
            sb.printf(t).printf(" := ")
            v.accept(this)
        }

    }

    override fun visit(sfcStep: SFCStep) {
        sb.nl().printf(if (sfcStep.isInitial) "INITIAL_STEP " else "STEP ")
        sb.printf(sfcStep.name).printf(":").increaseIndent()
        sfcStep.events.forEach { aa -> visit(aa) }
        sb.decreaseIndent().nl()
        sb.printf("END_STEP").nl()

    }

    private fun visit(aa: SFCStep.AssociatedAction) {
        sb.nl().printf(aa.actionName).append('(').append(aa.qualifier!!.qualifier.symbol)
        if (aa.qualifier!!.qualifier.hasTime) {
            sb.printf(", ")
            aa.qualifier!!.time.accept(this)
        }
        sb.printf(");")
    }

    override fun visit(sfcNetwork: SFCNetwork) {
        val seq = ArrayList(sfcNetwork.steps)
        seq.sortWith(compareBy(SFCStep::isInitial).thenBy(SFCStep::name))
        seq.forEach { a -> a.accept(this) }
        sfcNetwork.steps.stream()
                .flatMap { s -> s.incoming.stream() }
                .forEachOrdered { t -> t.accept(this) }

    }

    override fun visit(sfc: SFCImplementation) {
        //sfc.actions.forEach { a -> a.accept(this) }
        sfc.networks.forEach { n -> n.accept(this) }
    }

    override fun visit(transition: SFCTransition) {
        val f = transition.from!!.map { it.name }.reduce { a, b -> "$a, $b" }
        val t = transition.to!!.map { it.name }.reduce { a, b -> "$a, $b" }

        sb.nl().printf("TRANSITION FROM ")

        if (transition.from!!.size > 1) {
            sb.append('(').append(f).append(')')
        } else {
            sb.printf(f)
        }
        sb.printf(" TO ")
        if (transition.to!!.size > 1) {
            sb.append('(').append(t).append(')')
        } else {
            sb.printf(t)
        }
        sb.printf(" := ")

        transition.guard!!.accept(this)
        sb.printf(";").printf(" END_TRANSITION")

    }

    private fun printBody(stBody: StatementList?, sfcBody: SFCImplementation?) {
        when (bodyPrinting) {
            StructuredTextPrinter.BodyPrinting.ST -> if (stBody != null) {
                stBody.accept(this)
            } else {
                sfcBody?.accept(this)
            }
            StructuredTextPrinter.BodyPrinting.SFC -> if (sfcBody != null) {
                sfcBody.accept(this)
            } else {
                stBody?.accept(this)
            }
        }
    }

    /**
     *
     * clear.
     */

    fun clear() {
        sb = CodeWriter()
    }

    enum class BodyPrinting {
        ST, SFC
    }

    open class StringLiterals {
        open fun operator(operator: Operator?): String {
            return operator!!.symbol
        }

        fun assign(): String {
            return " := "
        }

        fun assignmentAttempt(): String {
            return " ?= "
        }

        fun statement_separator(): String {
            return ";"
        }

        fun exit(): String {
            return "EXIT"
        }

        open fun operator(operator: UnaryOperator): String? {
            return operator.symbol
        }

        fun comment_close(): String {
            return " *)"
        }

        fun comment_open(): String {
            return "(* "
        }

        fun repr(sv: Value<*, *>): String {
            return sv.dataType.repr(sv.value)
        }

        companion object {
            fun create(): StringLiterals {
                return StringLiterals()
            }
        }
    }

    companion object {
        /**
         * Constant `SL_ST`
         */
        var SL_ST = StringLiterals.create()
        /**
         * Constant `SL_SMV`
         */
        var SL_SMV: StringLiterals = object : StringLiterals() {
            override fun operator(operator: UnaryOperator): String {
                /*switch (operator) {
                case MINUS:
                    return "-";
                case NEGATE:
                    return "!";
            }*/
                return "<<unknown ue operator>>"
            }

            override fun operator(operator: Operator?): String {
                /*switch (operator) {
                case AND:
                    return "&";
                case OR:
                    return "|";
                case XOR:
                    return "xor";
                case NOT_EQUALS:
                    return "!=";
            }*/
                return operator!!.symbol
            }

            /*
        @Override
        public String repr(ScalarValue<? extends AnyDt, ?> sv) {
            if (sv.getDataType() instanceof AnyUnsignedInt) {
                AnyInt dataType = (AnyInt) sv.getDataType();
                return String.format("0ud%d_%d", 13, sv.getValue());
            }

            if (sv.getDataType() instanceof AnySignedInt) {
                AnyInt dataType = (AnyInt) sv.getDataType();
                return String.format("0sd%d_%d", 14, sv.getValue());
            }

            if (sv.getDataType() instanceof EnumerateType) {
                EnumerateType dataType = (EnumerateType) sv.getDataType();
                return sv.getValue().toString();
            }

            return super.repr(sv);
        }
        */
        }

        fun print(astNode: Top): String {
            val p = StructuredTextPrinter()
            astNode.accept(p)
            return p.string
        }
    }
}

