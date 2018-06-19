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

import com.google.common.collect.HashMultimap
import edu.kit.iti.formal.automation.datatypes.ArrayType
import edu.kit.iti.formal.automation.datatypes.IECString
import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.operators.Operator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.st.util.CodeWriter
import java.util.*

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
class StructuredTextPrinter
@JvmOverloads constructor(private val literals: StringLiterals = SL_ST) : AstVisitor<Unit>() {
    var sb = CodeWriter()
    var bodyPrinting = BodyPrinting.ST
    var isPrintComments: Boolean = false

    val string: String
        get() = sb.toString()


    override fun defaultVisit(visitable: Any) {
        throw IllegalArgumentException("not implemented: " + visitable!!::class.java)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {
        sb.append("ARRAY[")
        arrayTypeDeclaration.ranges.forEachIndexed {i,it->
            it.start.accept(this)
            sb.append("..")
            it.stop.accept(this)
            if(i<arrayTypeDeclaration.ranges.size-1)
                sb.append(", ")
        }
        sb.append("] OF ")
        sb.append(arrayTypeDeclaration.baseType.identifier!!)
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration) {
        sb.append("STRING")
    }

    override fun visit(elements: PouElements) {
        elements.forEach { it.accept(this) }
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(exitStatement: ExitStatement) {
        sb.append(literals.exit()).append(literals.statement_separator())

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
            sb.append("..")
            enumeration.stop!!.accept(this)
        }


    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression) {
        sb.append('(')
        binaryExpression.leftExpr!!.accept(this)
        sb.append(" ").append(literals.operator(binaryExpression.operator)).append(" ")
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
            sb.append(literals.assignmentAttempt())
        else
            sb.append(literals.assign())
        assignStatement.expression.accept(this)
        sb.append(";")

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
        sb.nl().append(enumerationTypeDeclaration.name).append(" : ")

        sb.append("(")

        for (s in enumerationTypeDeclaration.allowedValues)
            sb.append(s.text).append(" , ")

        sb.deleteLast(3)
        sb.append(");")


    }

    override fun visit(init: IdentifierInitializer) {
        sb.append(init.value!!)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement) {
        sb.nl()
        sb.append("REPEAT").increaseIndent()
        repeatStatement.statements.accept(this)

        sb.decreaseIndent().nl().append("UNTIL ")
        repeatStatement.condition.accept(this)
        sb.append("END_REPEAT")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement) {
        sb.nl()
        sb.append("WHILE ")
        whileStatement.condition.accept(this)
        sb.append(" DO ").increaseIndent()
        whileStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.append("END_WHILE")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression) {
        sb.append(literals.operator(unaryExpression.operator)!!).append(" ")
        unaryExpression.expression.accept(this)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations) {

        if (typeDeclarations.size > 0) {
            sb.append("TYPE ").increaseIndent()
            for (decl in typeDeclarations) {
                decl.accept(this)
            }
            sb.decreaseIndent().nl().append("END_TYPE").nl().nl()
        }

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(caseStatement: CaseStatement) {

        sb.nl().append("CASE ")
        caseStatement.expression!!.accept(this)
        sb.append(" OF ").increaseIndent()

        for (c in caseStatement.cases) {
            c.accept(this)
            sb.nl()
        }

        if (caseStatement.elseCase!!.size > 0) {
            sb.nl().append("ELSE ")
            caseStatement.elseCase!!.accept(this)
        }

        sb.nl().decreaseIndent().appendIdent().append("END_CASE;")

    }

    override fun visit(symbolicReference: SymbolicReference) {
        sb.append(symbolicReference.identifier)

        for (i in 0 until symbolicReference.derefCount)
            sb.append("^")

        if (symbolicReference.subscripts != null && !symbolicReference.subscripts!!.isEmpty()) {
            sb.append('[')
            for (expr in symbolicReference.subscripts!!) {
                expr.accept(this)
                sb.append(',')
            }
            sb.deleteLast()
            sb.append(']')
        }

        if (symbolicReference.sub != null) {
            sb.append(".")
            symbolicReference.sub!!.accept(this)
        }


    }

    /**
     * {@inheritDoc}
     */
    override fun visit(statements: StatementList) {
        for (stmt in statements) {
            if (stmt == null) {
                sb.append("{*ERROR: stmt null*}")
            } else {
                stmt.accept(this)
            }
        }

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(pd: ProgramDeclaration) {
        sb.append("PROGRAM ").append(pd.name).increaseIndent()
        pd.scope.accept(this)

        sb.nl()

        if (!pd.actions.isEmpty()) {
            pd.actions.forEach { v -> v.accept(this) }
            sb.nl()
        }

        printBody(pd.stBody, pd.sfcBody)

        sb.decreaseIndent().nl().append("END_PROGRAM").nl()

    }


    /*
     * TODO to new ast visitor
     *
     * @Override public Object accept(CaseExpression caseExpression) {
     * sb.append("CASES(").increaseIndent(); for (CaseExpression.Case cas :
     * caseExpression.getCases()) { cas.getCondition().accept(this); sb.append(
     * " -> "); cas.getExpression().accept(this); sb.append(";").nl(); }
     * sb.append("ELSE -> "); caseExpression.getElseExpression().accept(this);
     * sb.append(")").decreaseIndent(); ; }
     */

    /**
     * {@inheritDoc}
     */
    override fun visit(expressions: ExpressionList) {
        for (e in expressions) {
            e.accept(this)
            sb.append(", ")
        }
        sb.deleteLast(2)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(invocation: Invocation) {
        sb.append(invocation.calleeName).append("(")

        var params = false
        for (entry in invocation.parameters) {
            if (entry.name != null) {
                sb.append(entry.name!!)
                if (entry.isOutput)
                    sb.append(" => ")
                else
                    sb.append(" := ")
            }

            entry.expression.accept(this)
            sb.append(", ")
            params = true
        }

        if (params)
            sb.deleteLast(2)
        sb.append(");")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement) {
        sb.nl()
        sb.append("FOR ").append(forStatement.variable)
        sb.append(" := ")
        forStatement.start!!.accept(this)
        sb.append(" TO ")
        forStatement.stop!!.accept(this)
        sb.append(" DO ").increaseIndent()
        forStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.append("END_FOR")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        sb.append("FUNCTION_BLOCK ")

        /*
        if (functionBlockDeclaration.isFinal())
            sb.append("FINAL ");
        if (functionBlockDeclaration.isAbstract_())
            sb.append("ABSTRACT ");
        */

        sb.append(functionBlockDeclaration.name)

        /*String parent = functionBlockDeclaration.getParent().getName();
        if (parent != null)
            sb.append(" EXTENDS ").append(parent);

        String interfaces = functionBlockDeclaration.getInterfaces().stream()
                .map(RefTo::getName)
                .collect(Collectors.joining(", "));
        if (!interfaces.isEmpty())
            sb.append(" IMPLEMENTS ").append(interfaces);
        */

        sb.increaseIndent().nl()
        functionBlockDeclaration.scope.accept(this)
        sb.nl()

        /*if (!functionBlockDeclaration.getMethods().isEmpty()) {
            functionBlockDeclaration.getMethods().forEach(m -> m.accept(this));
            sb.nl();
        }*/

        if (!functionBlockDeclaration.actions.isEmpty()) {
            functionBlockDeclaration.actions.forEach { v -> v.accept(this) }
        }

        printBody(functionBlockDeclaration.stBody, functionBlockDeclaration.sfcBody)

        sb.decreaseIndent().nl().append("END_FUNCTION_BLOCK").nl().nl()

    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        sb.append("INTERFACE ").append(interfaceDeclaration.name)

        val extendsInterfaces = interfaceDeclaration.interfaces.map { it.identifier }
        if (!extendsInterfaces.isEmpty())
            sb.append(" EXTENDS ").append(extendsInterfaces)

        sb.increaseIndent().nl()

        //interfaceDeclaration.scope.accept(this)

        interfaceDeclaration.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().append("END_INTERFACE").nl().nl()

    }

    override fun visit(clazz: ClassDeclaration) {
        sb.append("CLASS ")

        if (clazz.isFinal)
            sb.append("FINAL ")
        if (clazz.isAbstract)
            sb.append("ABSTRACT ")

        sb.append(clazz.name)

        val parent = clazz.parent.identifier
        if (parent != null)
            sb.append(" EXTENDS ").append(parent)

        val interfaces = clazz.interfaces.map { it.identifier }
        if (!interfaces.isEmpty())
            sb.append(" IMPLEMENTS ").append(interfaces.joinToString(","))

        sb.increaseIndent().nl()

        clazz.scope.accept(this)

        clazz.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().append("END_CLASS").nl().nl()

    }

    override fun visit(method: MethodDeclaration) {
        sb.append("METHOD ")

        if (method.isFinal)
            sb.append("FINAL ")
        if (method.isAbstract)
            sb.append("ABSTRACT ")
        if (method.isOverride)
            sb.append("OVERRIDE ")

        sb.append(method.accessSpecifier.toString() + " ")

        sb.append(method.name)

        val returnType = method.returnTypeName
        if (!returnType!!.isEmpty())
            sb.append(" : $returnType")

        sb.increaseIndent().nl()

        method.scope.accept(this)

        method.stBody.accept(this)

        sb.decreaseIndent().nl().append("END_METHOD").nl().nl()

    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        sb.append("FUNCTION ").append(functionDeclaration.name)

        val returnType = functionDeclaration.returnType.identifier
        if (!(returnType == null || returnType.isEmpty()))
            sb.append(" : $returnType")

        sb.increaseIndent().nl()

        functionDeclaration.scope.accept(this)

        functionDeclaration.stBody?.accept(this)

        sb.decreaseIndent().nl().append("END_FUNCTION").nl().nl()

    }

    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration) {
        globalVariableListDeclaration.scope.accept(this)
        sb.nl()

    }

    override fun visit(referenceSpecification: ReferenceTypeDeclaration) {
        sb.append("REF_TO ")
        referenceSpecification.refTo?.accept(this)
    }

    override fun visit(referenceValue: ReferenceValue) {
        sb.append("REF(")
        referenceValue.referenceTo.accept(this)
        sb.append(")")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(returnStatement: ReturnStatement) {
        sb.appendIdent()
        sb.append("RETURN;")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(ifStatement: IfStatement) {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            sb.nl()

            if (i == 0)
                sb.append("IF ")
            else
                sb.append("ELSEIF ")

            ifStatement.conditionalBranches[i].condition.accept(this)

            sb.append(" THEN").increaseIndent()
            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.decreaseIndent()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.nl().append("ELSE").increaseIndent()
            ifStatement.elseBranch.accept(this)
            sb.decreaseIndent()
        }
        sb.nl().append("END_IF")

    }

    override fun visit(ad: ActionDeclaration) {
        sb.nl().append("ACTION ").append(ad.name).increaseIndent()
        printBody(ad.stBody, ad.sfcBody)
        sb.decreaseIndent().nl().append("END_ACTION")

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(fbc: InvocationStatement) {
        sb.nl()
        fbc.invocation.accept(this)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: Case) {
        sb.nl()
        for (cc in aCase.conditions) {
            cc.accept(this)
            sb.append(", ")
        }
        sb.deleteLast(2)
        sb.append(":")
        sb.increaseIndent()
        aCase.statements.accept(this)
        sb.decreaseIndent()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        sb.append(simpleTypeDeclaration.baseType.identifier!!)
        if (simpleTypeDeclaration.initialization != null) {
            sb.append(" := ")
            simpleTypeDeclaration.initialization!!.accept(this)
        }

    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        sb.append(structureTypeDeclaration.name)
        sb.append(": STRUCT").nl().increaseIndent()
        structureTypeDeclaration.fields.forEach { it ->
            sb.nl()
            it.accept(this)
        }
        sb.decreaseIndent().append("END_STRUCT;").nl()

    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration) {
        sb.append(subRangeTypeDeclaration.name)
        sb.append(": ").append(subRangeTypeDeclaration.baseType.identifier!!)
        sb.append("(")
        subRangeTypeDeclaration.range!!.start.accept(this)
        sb.append(" .. ")
        subRangeTypeDeclaration.range!!.stop.accept(this)
        sb.append(")")
        if (subRangeTypeDeclaration.initialization != null) {
            sb.append(" := ")
            subRangeTypeDeclaration.initialization!!.accept(this)
        }
        sb.append(";")

    }

    private fun variableDataType(vd: VariableDeclaration) {
        if (vd.dataType is ArrayType) {
            val dataType = vd.dataType as ArrayType
            sb.append(" ARRAY[")
            for (range in dataType.ranges) {
                range.start.accept(this)
                sb.append("..")
                range.stop.accept(this)
                sb.append(",")
            }
            sb.deleteLast()
            sb.append("] OF ").append(dataType.fieldType!!.name)
        } else {
            vd.typeDeclaration?.accept(this)
        }
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(commentStatement: CommentStatement) {
        if (isPrintComments) {
            sb.nl()
            sb.append(literals.comment_open())
            sb.append(commentStatement.comment)
            sb.append(literals.comment_close())
        }


    }

    /**
     * {@inheritDoc}
     */
    override fun visit(literal: Literal) {
        fun print(prefix: Any?, suffix: Any) =
                (if (prefix != null) "$prefix#" else "") + suffix

        sb.append(when (literal) {
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
        sb.append("[")
        initializations.initValues.forEach {
            it.accept(this)
            sb.append(", ")
        }
        // Added an extra ", "
        sb.deleteLast(2)
        sb.append("]")

    }

    override fun visit(localScope: Scope) {
        val variables = LookupList(localScope.variables)
        val varType = HashMultimap.create<Int, VariableDeclaration>(3, variables.size / 3 + 1)
        variables.forEach { v -> varType.put(v.type, v) }

        for (type in varType.keySet()) {
            val vars = ArrayList(varType.get(type!!))
            vars.sort()
            //By { a, b -> a.compareTo(b) }
            sb.nl().append("VAR")

            if (VariableDeclaration.INPUT and type >= VariableDeclaration.INOUT) {
                sb.append("_INOUT")
            } else {
                if (VariableDeclaration.INPUT and type != 0)
                    sb.append("_INPUT")
                if (VariableDeclaration.OUTPUT and type != 0)
                    sb.append("_OUTPUT")
                if (VariableDeclaration.EXTERNAL and type != 0)
                    sb.append("_EXTERNAL")
                if (VariableDeclaration.GLOBAL and type != 0)
                    sb.append("_GLOBAL")
                if (VariableDeclaration.TEMP and type != 0)
                    sb.append("TEMP")
            }
            sb.append(" ")
            if (VariableDeclaration.CONSTANT and type != 0)
                sb.append("CONSTANT ")
            if (VariableDeclaration.RETAIN and type != 0)
                sb.append("RETAIN ")
            sb.increaseIndent()
            for (vd in vars) {
                sb.nl()
                sb.append(vd.name).append(" : ")
                variableDataType(vd)
                if (vd.init != null) {
                    sb.append(" := ")
                    vd.init!!.accept(this)
                }
                sb.append(";")
            }
            sb.decreaseIndent().nl().append("END_VAR")
            sb.nl()
        }

    }

    override fun visit(structureInitialization: StructureInitialization) {
        sb.append("(")
        structureInitialization.initValues.entries.stream().forEach { initialization ->
            sb.append(initialization.key).append(" := ")
            initialization.value.accept(this)
            sb.append(", ")
        }
        // Added an extra ", "
        sb.deleteLast(2)
        sb.append(")")

    }

    override fun visit(sfcStep: SFCStep) {
        sb.nl().append(if (sfcStep.isInitial) "INITIAL_STEP " else "STEP ")
        sb.append(sfcStep.name).append(":").increaseIndent()
        sfcStep.events.forEach { aa -> visit(aa) }
        sb.decreaseIndent().nl()
        sb.append("END_STEP").nl()

    }

    private fun visit(aa: SFCStep.AssociatedAction) {
        sb.nl().append(aa.actionName!!).append('(').append(aa.qualifier!!.qualifier!!.symbol)
        if (aa.qualifier!!.qualifier!!.hasTime) {
            sb.append(", ")
            aa.qualifier!!.time!!.accept(this)
        }
        sb.append(");")
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
        sfc.actions.forEach { a -> a.accept(this) }
        sfc.networks.forEach { n -> n.accept(this) }

    }

    override fun visit(transition: SFCTransition) {
        val f = transition.from!!.map { it.name }.reduce { a, b -> "$a, $b" }
        val t = transition.to!!.map { it.name }.reduce { a, b -> "$a, $b" }

        sb.nl().append("TRANSITION FROM ")

        if (transition.from!!.size > 1) {
            sb.append('(').append(f).append(')')
        } else {
            sb.append(f)
        }
        sb.append(" TO ")
        if (transition.to!!.size > 1) {
            sb.append('(').append(t).append(')')
        } else {
            sb.append(t)
        }
        sb.append(" := ")

        transition.guard!!.accept(this)
        sb.append(";").append(" END_TRANSITION")

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
