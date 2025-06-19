/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.IECString
import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.il.IlPrinter
import edu.kit.iti.formal.automation.operators.Operator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto
import java.util.*

private val QUOTED_IDENTIFIER = listOf("STEP", "END_STEP", "TRANSITION", "END_TRANSITION", "INITIAL_STEP", "FROM")

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
open class StructuredTextPrinter(var sb: CodeWriter = CodeWriter()) : AstVisitor<Unit>() {
    private val literals: KeywordRepr = keywords
    var bodyPrintingOrder = listOf(BodyPrinting.ST, BodyPrinting.SFC, BodyPrinting.IL)
    var isPrintComments: Boolean = false

    val string: String
        get() = sb.toString()

    override fun defaultVisit(obj: Any): Unit = throw IllegalArgumentException("not implemented: " + obj::class.java)

    override fun visit(blockStatement: BlockStatement) {
        sb.nl().print("//! REGION ${blockStatement.name}")
        blockParam(blockStatement.state, "[", "]")
        blockParam(blockStatement.input, "(", ")")
        sb.write(" => ")
        blockParam(blockStatement.output, "(", ")")
        sb.increaseIndent()
        blockStatement.statements.accept(this)
        sb.decreaseIndent()
        sb.nl().print("//! END_REGION")
    }

    private fun blockParam(p: MutableList<SymbolicReference>, pre: String, suf: String) =
        p.joinInto(sb, ", ", pre, suf) {
            it.accept(this@StructuredTextPrinter)
        }

    override fun visit(empty: EMPTY_EXPRESSION) {
        sb.print("(* empty expression *)")
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {
        sb.printf("ARRAY[")
        arrayTypeDeclaration.ranges.forEachIndexed { i, it ->
            it.start.accept(this)
            sb.printf("..")
            it.stop.accept(this)
            if (i < arrayTypeDeclaration.ranges.size - 1) {
                sb.printf(", ")
            }
        }
        sb.printf("] OF ")
        sb.printf(arrayTypeDeclaration.type.name)
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration) {
        sb.printf("STRING")
    }

    override fun visit(elements: PouElements) {
        elements.forEach { it.accept(this) }
    }

    override fun visit(exitStatement: ExitStatement) {
        sb.printf(literals.exit()).printf(literals.statementSeparator())
    }

    override fun visit(integerCondition: CaseCondition.IntegerCondition) {
        sb.appendIdent()
        integerCondition.value.accept(this)
    }

    override fun visit(enumeration: CaseCondition.Enumeration) {
        if (enumeration.start == enumeration.stop) {
            enumeration.start.accept(this)
        } else {
            enumeration.start.accept(this)
            sb.printf("..")
            enumeration.stop!!.accept(this)
        }
    }

    override fun visit(binaryExpression: BinaryExpression) {
        sb.append('(')
        binaryExpression.leftExpr.accept(this)
        sb.space().printf(literals.operator(binaryExpression.operator)).space()
        binaryExpression.rightExpr.accept(this)
        sb.append(')')
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        sb.nl()
        assignmentStatement.location.accept(this)
        if (assignmentStatement.isAssignmentAttempt) {
            sb.printf(literals.assignmentAttempt())
        } else {
            sb.printf(literals.assign())
        }
        assignmentStatement.expression.accept(this)
        sb.printf(";")
    }

    override fun visit(configurationDeclaration: ConfigurationDeclaration) {
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        sb.nl().printf(enumerationTypeDeclaration.name).printf(" : ")
        enumerationTypeDeclaration.allowedValues.joinTo(sb, ", ", "(", ");") {
            it.text
        }
    }

    override fun visit(init: IdentifierInitializer) {
        sb.printf(init.value!!)
    }

    override fun visit(repeatStatement: RepeatStatement) {
        sb.nl()
        sb.printf("REPEAT").increaseIndent()
        repeatStatement.statements.accept(this)

        sb.decreaseIndent().nl().printf("UNTIL ")
        repeatStatement.condition.accept(this)
        sb.printf("END_REPEAT")
    }

    override fun visit(whileStatement: WhileStatement) {
        sb.nl()
        sb.printf("WHILE ")
        whileStatement.condition.accept(this)
        sb.printf(" DO ").increaseIndent()
        whileStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("END_WHILE")
    }

    override fun visit(unaryExpression: UnaryExpression) {
        sb.printf(literals.operator(unaryExpression.operator)!!).space()
        unaryExpression.expression.accept(this)
    }

    override fun visit(typeDeclarations: TypeDeclarations) {
        if (typeDeclarations.size > 0) {
            sb.printf("TYPE ").increaseIndent()
            for (decl in typeDeclarations) {
                decl.accept(this)
            }
            sb.decreaseIndent().nl().printf("END_TYPE").nl().nl()
        }
    }

    override fun visit(caseStatement: CaseStatement) {
        sb.nl().printf("CASE ")
        caseStatement.expression.accept(this)
        sb.printf(" OF ").increaseIndent()

        for (c in caseStatement.cases) {
            c.accept(this)
            sb.nl()
        }

        if (caseStatement.elseCase.size > 0) {
            sb.nl().printf("ELSE ")
            caseStatement.elseCase.accept(this)
        }

        sb.nl().decreaseIndent().appendIdent().printf("END_CASE")
    }

    override fun visit(symbolicReference: SymbolicReference) {
        sb.printf(quoteIdentifier(symbolicReference.identifier))

        for (i in 0 until symbolicReference.derefCount) {
            sb.printf("^")
        }

        if (symbolicReference.subscripts != null && !symbolicReference.subscripts!!.isEmpty()) {
            symbolicReference.subscripts!!.joinInto(sb, ", ", "[", "]") { it.accept(this) }
        }

        if (symbolicReference.sub != null) {
            sb.printf(".")
            symbolicReference.sub!!.accept(this)
        }
    }

    private fun quoteIdentifier(identifier: String): String = if (identifier.uppercase(Locale.getDefault()) in
        QUOTED_IDENTIFIER
    ) {
        "`$identifier`"
    } else {
        identifier
    }

    override fun visit(statements: StatementList) {
        for (stmt in statements) {
            stmt.accept(this)
        }
    }

    override fun visit(programDeclaration: ProgramDeclaration) {
        printComment(programDeclaration.comment)
        sb.keyword("PROGRAM").space().printf(programDeclaration.name).increaseIndent().nl()
        programDeclaration.scope.accept(this)

        sb.nl()

        if (!programDeclaration.actions.isEmpty()) {
            programDeclaration.actions.forEach { v -> v.accept(this) }
            sb.nl()
        }

        printBody(programDeclaration)

        sb.decreaseIndent().nl().keyword("END_PROGRAM").nl()
    }

    override fun visit(expressions: ExpressionList) {
        expressions.joinInto(sb) { it.accept(this) }
    }

    override fun visit(invocation: Invocation) {
        invocation.callee.accept(this)
        visitInvocationParameter(invocation.parameters)
    }

    private fun visitInvocationParameter(parameters: MutableList<InvocationParameter>) {
        parameters.joinInto(sb, ", ", "(", ")") {
            if (it.name != null) {
                sb.printf(it.name!!)
                if (it.isOutput) {
                    sb.printf(" => ")
                } else {
                    sb.printf(" := ")
                }
            }
            it.expression.accept(this)
        }
    }

    override fun visit(forStatement: ForStatement) {
        sb.nl()
        sb.printf("FOR ").printf(forStatement.variable)
        sb.printf(" := ")
        forStatement.start.accept(this)
        sb.printf(" TO ")
        forStatement.stop.accept(this)
        sb.printf(" DO ").increaseIndent()
        forStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("END_FOR")
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        printComment(functionBlockDeclaration.comment)
        sb.keyword("FUNCTION_BLOCK ")
        if (functionBlockDeclaration.isFinal) {
            sb.keyword("FINAL ")
        }
        if (functionBlockDeclaration.isAbstract) {
            sb.keyword("ABSTRACT ")
        }

        sb.printf(functionBlockDeclaration.name)

        if (functionBlockDeclaration.parent.identifier != null) {
            sb.keyword(" EXTENDS ").printf(functionBlockDeclaration.parent.identifier!!)
        }

        if (functionBlockDeclaration.interfaces.isNotEmpty()) {
            val interf = functionBlockDeclaration.interfaces
                .map { it.identifier!! }
                .joinToString(", ")
            sb.keyword(" IMPLEMENTS ").printf(interf)
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

        printBody(functionBlockDeclaration)

        sb.decreaseIndent().nl().printf("END_FUNCTION_BLOCK").nl().nl()
    }

    private fun printComment(comment: String) {
        if (comment.isNotBlank()) {
            sb.printf(literals.commentOpen())
            sb.printf(comment)
            sb.printf(literals.commentClose() + "\n")
        }
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        sb.keyword("INTERFACE ").printf(interfaceDeclaration.name)

        if (!interfaceDeclaration.interfaces.isEmpty()) {
            sb.keyword(" EXTENDS ")
            sb.print(interfaceDeclaration.interfaces.joinToString(", ") { it.identifier!! })
        }

        sb.increaseIndent().nl()

        // interfaceDeclaration.scope.accept(this)

        interfaceDeclaration.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().keyword("END_INTERFACE").nl().nl()
    }

    override fun visit(clazz: ClassDeclaration) {
        printComment(clazz.comment)
        sb.keyword("CLASS ")

        if (clazz.isFinal) {
            sb.keyword("FINAL ")
        }
        if (clazz.isAbstract) {
            sb.keyword("ABSTRACT ")
        }

        sb.printf(clazz.name)

        val parent = clazz.parent.identifier
        if (parent != null) {
            sb.keyword(" EXTENDS ").printf(parent)
        }

        val interfaces = clazz.interfaces.map { it.identifier }
        if (!interfaces.isEmpty()) {
            sb.keyword(" IMPLEMENTS ").printf(interfaces.joinToString(","))
        }

        sb.increaseIndent().nl()

        clazz.scope.accept(this)

        clazz.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().keyword("END_CLASS").nl().nl()
    }

    override fun visit(method: MethodDeclaration) {
        sb.keyword("METHOD ")

        sb.printf(method.accessSpecifier.toString() + " ")

        if (method.isFinal) {
            sb.keyword("FINAL ")
        }
        if (method.isAbstract) {
            sb.keyword("ABSTRACT ")
        }
        if (method.isOverride) {
            sb.keyword("OVERRIDE ")
        }

        sb.printf(method.name)

        val returnType = method.returnTypeName
        if (!returnType!!.isEmpty()) {
            sb.printf(" : $returnType")
        }

        sb.increaseIndent().nl()

        method.scope.accept(this)

        method.stBody.accept(this)

        sb.decreaseIndent().nl().keyword("END_METHOD").nl().nl()
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        printComment(functionDeclaration.comment)
        sb.keyword("FUNCTION ").printf(functionDeclaration.name)

        val returnType = functionDeclaration.returnType.identifier
        if (!(returnType == null || returnType.isEmpty())) {
            sb.printf(" : $returnType")
        }

        sb.increaseIndent().nl()

        functionDeclaration.scope.accept(this)

        printBody(functionDeclaration)

        sb.decreaseIndent().nl().keyword("END_FUNCTION").nl().nl()
    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration) {
        gvlDecl.scope.accept(this)
        sb.nl()
    }

    override fun visit(referenceSpecification: ReferenceTypeDeclaration) {
        sb.keyword("REF_TO ")
        referenceSpecification.refTo.accept(this)
    }

    override fun visit(referenceValue: ReferenceValue) {
        sb.keyword("REF(")
        referenceValue.referenceTo.accept(this)
        sb.printf(")")
    }

    override fun visit(returnStatement: ReturnStatement) {
        sb.nl().keyword("RETURN;")
    }

    override fun visit(ifStatement: IfStatement) {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            sb.nl()

            if (i == 0) {
                sb.keyword("IF")
                sb.space()
            } else {
                sb.keyword("ELSIF ")
                sb.space()
            }
            ifStatement.conditionalBranches[i].condition.accept(this)

            sb.space().keyword("THEN").increaseIndent()
            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.decreaseIndent()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.nl().keyword("ELSE").increaseIndent()
            ifStatement.elseBranch.accept(this)
            sb.decreaseIndent()
        }
        sb.nl().keyword("END_IF")
    }

    override fun visit(actionDeclaration: ActionDeclaration) {
        sb.nl().keyword("ACTION").space().printf(actionDeclaration.name).increaseIndent()
        printBody(actionDeclaration)
        sb.decreaseIndent().nl().keyword("END_ACTION")
    }

    override fun visit(invocation: InvocationStatement) {
        sb.nl()
        invocation.callee.accept(this)
        visitInvocationParameter(invocation.parameters)
        sb.printf(";")
    }

    override fun visit(aCase: Case) {
        sb.nl()
        aCase.conditions.joinInto(sb) { it.accept(this) }
        sb.printf(":")
        sb.block {
            aCase.statements.accept(this@StructuredTextPrinter)
        }
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        sb.printf(simpleTypeDeclaration.baseType.identifier!!)
        /*if (simpleTypeDeclaration.initialization != null) {
            sb.printf(" := ")
            simpleTypeDeclaration.initialization!!.accept(this)
        }*/
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        sb.printf(structureTypeDeclaration.name)
        sb.printf(": ").keyword("STRUCT").nl().increaseIndent()
        structureTypeDeclaration.fields.forEach { it ->
            sb.nl()
            it.accept(this)
        }
        sb.decreaseIndent().keyword("END_STRUCT").write(";").nl()
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

    override fun visit(vd: VariableDeclaration) {
        sb.write("${vd.name} :")
        variableDataType(vd)
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

    fun variableDataType(dt: AnyDt) {
        sb.printf(dt.reprDecl())
    }

    override fun visit(commentStatement: CommentStatement) {
        if (isPrintComments) {
            sb.nl()
            if ('\n' in commentStatement.comment) {
                sb.comment(literals.commentOpen() + commentStatement.comment + literals.commentClose())
            } else {
                sb.comment("//%s\n", commentStatement.comment)
            }
        }
    }

    override fun visit(literal: Literal) {
        fun print(prefix: Any?, suffix: Any) = (if (prefix != null) "$prefix#" else "") + suffix

        sb.printf(
            when (literal) {
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
                    print(literal.dataType().name, "$y-$mo-$d-$h:$m:$s.$ms")
                }

                is StringLit -> {
                    if (literal.dataType() is IECString.WSTRING) {
                        "\"${literal.value}\""
                    } else {
                        "'${literal.value}'"
                    }
                }

                is NullLit -> "null"
                is TimeLit -> {
                    print(literal.dataType().name, "${literal.value.milliseconds}ms")
                }

                is BooleanLit -> literal.value.toString().uppercase(Locale.getDefault())
                is BitLit -> {
                    print(literal.dataType.obj?.name, "2#" + literal.value.toString(2))
                }

                is UnindentifiedLit -> literal.value
            },
        )
    }

    override fun visit(arrayinit: ArrayInitialization) {
        arrayinit.initValues.joinInto(sb, ", ", "[", "]") {
            it.accept(this)
        }
    }

    override fun visit(localScope: Scope) {
        val variables = VariableScope(localScope.variables)
        variables.groupBy { it.type }
            .forEach { (type, v) ->
                val vars = v.toMutableList()
                vars.sortWith(compareBy { it.name })

                // By { a, b -> a.compareTo(b) }

                if (VariableDeclaration.INPUT and type >= VariableDeclaration.INOUT) {
                    sb.nl().keyword("VAR_INOUT")
                } else {
                    when {
                        VariableDeclaration.INPUT and type != 0 -> sb.keyword("VAR_INPUT")
                        VariableDeclaration.OUTPUT and type != 0 -> sb.keyword("VAR_OUTPUT")
                        VariableDeclaration.EXTERNAL and type != 0 -> sb.keyword("VAR_EXTERNAL")
                        VariableDeclaration.GLOBAL and type != 0 -> sb.keyword("VAR_GLOBAL")
                        VariableDeclaration.TEMP and type != 0 -> sb.keyword("VAR_TEMP")
                        else -> sb.keyword("VAR")
                    }
                }
                sb.space()
                if (VariableDeclaration.CONSTANT and type != 0) {
                    sb.keyword("CONSTANT ")
                }
                if (VariableDeclaration.RETAIN and type != 0) {
                    sb.keyword("RETAIN ")
                }
                sb.space()
                sb.increaseIndent()
                for (vd in vars) {
                    print(vd)
                }
                sb.decreaseIndent().nl().keyword("END_VAR")
                sb.nl()
            }
    }

    open fun print(vd: VariableDeclaration) {
        sb.nl()
        sb.printf(vd.name).printf(" : ")
        variableDataType(vd)
        when {
            vd.initValue != null -> {
                sb.printf(" := ")
                val (dt, v) = vd.initValue as Value<*, *>
                sb.printf(dt.repr(v))
            }

            vd.init != null -> {
                sb.printf(" := ")
                vd.init!!.accept(this)
            }
        }
        sb.printf(";")
    }

    override fun visit(structureInitialization: StructureInitialization) {
        structureInitialization.initValues.joinInto(sb, ", ", "(", ")") { t, v ->
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
        // sfc.actions.forEach { a -> a.accept(this) }
        sfc.networks.forEach { n -> n.accept(this) }
    }

    override fun visit(transition: SFCTransition) {
        val f = transition.from.map { it.name }.reduce { a, b -> "$a, $b" }
        val t = transition.to.map { it.name }.reduce { a, b -> "$a, $b" }

        sb.nl().keyword("TRANSITION").space().keyword("FROM").space()

        if (transition.from.size > 1) {
            sb.append('(').append(f).append(')')
        } else {
            sb.printf(f)
        }
        sb.space().keyword("TO").space()
        if (transition.to.size > 1) {
            sb.append('(').append(t).append(')')
        } else {
            sb.printf(t)
        }
        sb.printf(" := ")

        transition.guard.accept(this)
        sb.printf(";").space().keyword("END_TRANSITION")
    }

    private fun printBody(a: HasBody) {
        val stBody = a.stBody
        val sfcBody = a.sfcBody
        val ilBody = a.ilBody

        loop@ for (type in bodyPrintingOrder) {
            when (type) {
                BodyPrinting.ST -> stBody?.accept(this) ?: continue@loop
                BodyPrinting.SFC -> sfcBody?.accept(this) ?: continue@loop
                BodyPrinting.IL -> ilBody?.accept(IlPrinter(sb)) ?: continue@loop
            }
            break@loop
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
        ST,
        SFC,
        IL,
    }

    open class KeywordRepr {
        open fun operator(operator: Operator?): String = operator!!.symbol

        fun assign(): String = " := "

        fun assignmentAttempt(): String = " ?= "

        fun statementSeparator(): String = ";"

        fun exit(): String = "EXIT"

        open fun operator(operator: UnaryOperator): String? = operator.symbol

        fun commentClose(): String = " *)"

        fun commentOpen(): String = "(* "

        fun repr(sv: Value<*, *>): String = sv.dataType.repr(sv.value)
    }

    companion object {
        var keywords = KeywordRepr()

        fun print(astNode: Top): String {
            val p = StructuredTextPrinter()
            astNode.accept(p)
            return p.string
        }
    }

    override fun visit(jump: JumpStatement) {
        sb.nl().write("JMP ${jump.target};")
    }

    override fun visit(label: LabelStatement) {
        sb.nl().write("${label.label}:")
    }

    override fun visit(special: SpecialStatement) {
        when (special) {
            is SpecialStatement.Assert -> {
                sb.nl().write("//# assert ")
                special.name?.let { sb.write(": $it") }
                special.exprs.joinInto(sb, separator = ", ") { it.accept(this) }
            }

            is SpecialStatement.Assume -> {
                sb.nl().write("//# assume ")
                special.name?.let { sb.write(": $it") }
                special.exprs.joinInto(sb, separator = ", ") { it.accept(this) }
            }

            is SpecialStatement.Havoc -> {
                sb.nl().write("//# havoc ")
                special.name?.let { sb.write(": $it") }
                special.variables.joinInto(sb, separator = ", ") { it.accept(this) }
            }

            else -> sb.nl().write("// special statement of type $special not supported")
        }
    }
}