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

import edu.kit.iti.formal.automation.*
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.il.*
import edu.kit.iti.formal.automation.operators.*
import edu.kit.iti.formal.automation.scope.*
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.*
import edu.kit.iti.formal.automation.visitors.*
import edu.kit.iti.formal.util.Builder
import io.github.wadoon.pp.*
import java.util.*

private val QUOTED_IDENTIFIER = listOf("STEP", "END_STEP", "TRANSITION", "END_TRANSITION", "INITIAL_STEP", "FROM")

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
open class PPStructuredTextPrinter : AstVisitor<Document>() {
    private val literals: KeywordRepr = keywords
    var bodyPrintingOrder = listOf(BodyPrinting.ST, BodyPrinting.SFC, BodyPrinting.IL)
    var isPrintComments: Boolean = false

    val string: String
        get() = toString()

    override fun defaultVisit(obj: Any) = throw IllegalArgumentException("not implemented: " + obj::class.java)

    private fun build(f: Builder.() -> Unit): Document {
        val builder = Builder()
        f(builder)
        return builder.doc
    }

    override fun visit(blockStatement: BlockStatement) = build {
        nl()
        +(
            "//! REGION ${blockStatement.name} " + blockParam(blockStatement.state, "[", "]") +
                blockParam(blockStatement.input, "(", ")") +
                " => " +
                blockParam(blockStatement.output, "(", ")")
            )
        indent {
            accept(blockStatement.statements)
        }
        nl()
        +"//! END_REGION"
    }

    private fun accept(ctx: Visitable?) =
        ctx?.accept(this@PPStructuredTextPrinter) ?: empty

    private fun blockParam(p: MutableList<SymbolicReference>, pre: String, suf: String) =
        p.joinToString(", ", pre, suf) { it.toString() }

    override fun visit(empty: EMPTY_EXPRESSION) = build {
        +"(* empty expression *)"
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) = build {
        +"ARRAY["
        arrayTypeDeclaration.ranges.forEachIndexed { i, it ->
            accept(it.start)
            +".."
            accept(it.stop)
            if (i < arrayTypeDeclaration.ranges.size - 1) {
                +", "
            }
        }
        +"] OF "
        +arrayTypeDeclaration.type.name
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration) = build {
        +"STRING"
    }

    override fun visit(elements: PouElements) = elements.joinToDocument(hardline + hardline) { accept(it) }

    override fun visit(exitStatement: ExitStatement) = build {
        +literals.exit()
        +literals.statementSeparator()
    }

    override fun visit(integerCondition: CaseCondition.IntegerCondition) = build {
        indent {
            accept(integerCondition.value)
        }
    }

    override fun visit(enumeration: CaseCondition.Enumeration) =
        if (enumeration.start == enumeration.stop) {
            accept(enumeration.start)
        } else {
            concat(accept(enumeration.start), string(".."), accept(enumeration.stop))
        }

    override fun visit(binaryExpression: BinaryExpression) = build {
        +'('
        accept(binaryExpression.leftExpr)
        space()
        +literals.operator(binaryExpression.operator)
        space()
        accept(binaryExpression.rightExpr)
        +')'
    }

    override fun visit(assignmentStatement: AssignmentStatement) = build {
        nl()
        accept(assignmentStatement.location)
        if (assignmentStatement.isAssignmentAttempt) {
            +literals.assignmentAttempt()
        } else {
            +literals.assign()
        }
        accept(assignmentStatement.expression)
        +";"
    }

    override fun visit(configurationDeclaration: ConfigurationDeclaration) = build {
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) = build {
        nl()
        +enumerationTypeDeclaration.name
        +" : "
        +lparen
        +hang(4, enumerationTypeDeclaration.allowedValues.joinToDocument(commaSpace) { string(it.text)})
        +rparen
        +semi
    }

    override fun visit(init: IdentifierInitializer) = build {
        +init.value!!
    }

    override fun visit(repeatStatement: RepeatStatement) = build {
        nl()
        +"REPEAT"
        +break1
        indent {
            accept(repeatStatement.statements)
        }
        +break1
        printf("UNTIL")
        +break1
        accept(repeatStatement.condition)
        +"END_REPEAT"
    }

    override fun visit(whileStatement: WhileStatement) = build {
        nl()
        +"WHILE "
        accept(whileStatement.condition)
        +" DO "
        indent {
            accept(whileStatement.statements)
        }
        +"END_WHILE"
    }

    override fun visit(unaryExpression: UnaryExpression) = build {
        +literals.operator(unaryExpression.operator)!!
        space()
        accept(unaryExpression.expression)
    }

    override fun visit(typeDeclarations: TypeDeclarations) = build {
        if (typeDeclarations.size > 0) {
            +"TYPE "
            indent {
                for (decl in typeDeclarations) {
                    +accept(decl)
                }
            }
            nl()
            +"END_TYPE"
            nl().nl()
        }
    }

    override fun visit(caseStatement: CaseStatement) = build {
        nl()
        +"CASE "
        accept(caseStatement.expression)
        +" OF "
        indent {

            for (c in caseStatement.cases) {
                accept(c)
                nl()
            }

            if (caseStatement.elseCase.size > 0) {
                nl()
                +"ELSE "
                accept(caseStatement.elseCase)
            }

            nl()
        }
        printf("END_CASE")
    }

    override fun visit(symbolicReference: SymbolicReference) = build {
        +quoteIdentifier(symbolicReference.identifier)

        for (i in 0 until symbolicReference.derefCount) {
            +"^"
        }

        if (symbolicReference.subscripts != null && !symbolicReference.subscripts!!.isEmpty()) {
            +(lbracket + symbolicReference.subscripts!!.flowMap(commaSpace) { accept(it) } + rbracket)
        }

        if (symbolicReference.sub != null) {
            +dot
            accept(symbolicReference.sub)
        }
    }

    private fun quoteIdentifier(identifier: String): String = if (identifier.uppercase(Locale.getDefault()) in
        QUOTED_IDENTIFIER
    ) {
        "`$identifier`"
    } else {
        identifier
    }

    override fun visit(statements: StatementList) = build {
        for (stmt in statements) {
            accept(stmt)
        }
    }

    override fun visit(programDeclaration: ProgramDeclaration) = build {
        printComment(programDeclaration.comment)
        keyword("PROGRAM").space()
        +programDeclaration.name
        indent {
            nl()
            +visit(programDeclaration.scope)
            nl()

            if (!programDeclaration.actions.isEmpty()) {
                programDeclaration.actions.forEach { v -> accept(v) }
                nl()
            }

            printBody(programDeclaration)
        }
        nl().keyword("END_PROGRAM").nl()
    }

    override fun visit(expressions: ExpressionList) = expressions.joinToDocument { accept(it) }

    override fun visit(invocation: Invocation) = build {
        +accept(invocation.callee)
        +visitInvocationParameter(invocation.parameters)
    }

    private fun visitInvocationParameter(parameters: MutableList<InvocationParameter>) =
        lparen + parameters.flowMap(sep = commaSpace) { it: InvocationParameter ->
            if (it.name != null) {
                string(it.name!!) + space + string(if (it.isOutput) "=>" else ":=") + space
            } else {
                empty
            } + accept(it.expression)
        } + rparen

    override fun visit(forStatement: ForStatement) = build {
        nl()
        +"FOR "
        +forStatement.variable
        +" := "
        accept(forStatement.start)
        +" TO "
        accept(forStatement.stop)
        +" DO "
        indent {
            accept(forStatement.statements)
        }
        nl()
        +"END_FOR"
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) = build {
        printComment(functionBlockDeclaration.comment)
        keyword("FUNCTION_BLOCK ")
        if (functionBlockDeclaration.isFinal) {
            keyword("FINAL ")
        }
        if (functionBlockDeclaration.isAbstract) {
            keyword("ABSTRACT ")
        }

        +functionBlockDeclaration.name

        if (functionBlockDeclaration.parent.identifier != null) {
            keyword(" EXTENDS ")
            +functionBlockDeclaration.parent.identifier!!
        }

        if (functionBlockDeclaration.interfaces.isNotEmpty()) {
            val interf = functionBlockDeclaration.interfaces
                .map { it.identifier!! }
                .joinToString(", ")
            keyword(" IMPLEMENTS ")
            +interf
        }
        indent {
            nl()
            visit(functionBlockDeclaration.scope)
            nl()

            if (functionBlockDeclaration.methods.isNotEmpty()) {
                functionBlockDeclaration.methods.forEach { accept(it) }
                nl()
            }

            if (!functionBlockDeclaration.actions.isEmpty()) {
                functionBlockDeclaration.actions.forEach { v -> accept(v) }
            }

            printBody(functionBlockDeclaration)
        }
        nl()
        +"END_FUNCTION_BLOCK"
        nl().nl()
    }

    private fun printComment(comment: String) = build {
        if (comment.isNotBlank()) {
            +literals.commentOpen()
            +comment
            +(literals.commentClose() + "\n")
        }
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) = build {
        keyword("INTERFACE ")
        +interfaceDeclaration.name

        if (!interfaceDeclaration.interfaces.isEmpty()) {
            keyword(" EXTENDS ")
            +interfaceDeclaration.interfaces.joinToString(", ") { it.identifier!! }
        }

        indent {
            nl()

            // accept(interfaceDeclaration.scope)

            interfaceDeclaration.methods.forEach { m -> accept(m) }
        }
        nl()
        keyword("END_INTERFACE").nl().nl()
    }

    override fun visit(clazz: ClassDeclaration) = build {
        printComment(clazz.comment)
        keyword("CLASS ")

        if (clazz.isFinal) {
            keyword("FINAL ")
        }
        if (clazz.isAbstract) {
            keyword("ABSTRACT ")
        }

        +clazz.name

        val parent = clazz.parent.identifier
        if (parent != null) {
            keyword(" EXTENDS ")
            +parent
        }

        val interfaces = clazz.interfaces.map { it.identifier }
        if (!interfaces.isEmpty()) {
            keyword(" IMPLEMENTS ")
            +interfaces.joinToString(",")
        }

        indent {
            nl()
            +visit(clazz.scope)
            clazz.methods.forEach { m -> accept(m) }
        }
        nl()
        keyword("END_CLASS").nl().nl()
    }

    override fun visit(method: MethodDeclaration) = build {
        keyword("METHOD ")

        +(method.accessSpecifier.toString() + " ")

        if (method.isFinal) {
            keyword("FINAL ")
        }
        if (method.isAbstract) {
            keyword("ABSTRACT ")
        }
        if (method.isOverride) {
            keyword("OVERRIDE ")
        }

        +method.name

        val returnType = method.returnTypeName
        if (!returnType!!.isEmpty()) {
            +" : $returnType"
        }

        indent {
            nl()
            +visit(method.scope)
            +accept(method.stBody)
        }
        nl()
        keyword("END_METHOD")
        nl()
        nl()
    }

    override fun visit(functionDeclaration: FunctionDeclaration) = build {
        printComment(functionDeclaration.comment)
        keyword("FUNCTION ")
        +functionDeclaration.name

        val returnType = functionDeclaration.returnType.identifier
        if (!(returnType == null || returnType.isEmpty())) {
            +" : $returnType"
        }

        indent {
            nl()
            +visit(functionDeclaration.scope)
            +printBody(functionDeclaration)
        }
        nl()
        keyword("END_FUNCTION").nl().nl()
    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration) = build {
        +visit(gvlDecl.scope)
        nl()
    }

    override fun visit(referenceSpecification: ReferenceTypeDeclaration) = build {
        keyword("REF_TO ")
        accept(referenceSpecification.refTo)
    }

    override fun visit(referenceValue: ReferenceValue) = build {
        keyword("REF(")
        accept(referenceValue.referenceTo)
        +")"
    }

    override fun visit(returnStatement: ReturnStatement) = build {
        nl().keyword("RETURN;")
    }

    override fun visit(ifStatement: IfStatement) = build {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            nl()

            if (i == 0) {
                keyword("IF")
                space()
            } else {
                keyword("ELSIF ")
                space()
            }
            accept(ifStatement.conditionalBranches[i].condition)

            space().keyword("THEN")
            indent {
                accept(ifStatement.conditionalBranches[i].statements)
            }

            if (ifStatement.elseBranch.size > 0) {
                nl().keyword("ELSE")
                indent {
                    accept(ifStatement.elseBranch)
                }
                nl().keyword("END_IF")
            }
        }
    }

    override fun visit(actionDeclaration: ActionDeclaration) = build {
        nl().keyword("ACTION").space()
        +actionDeclaration.name
        indent {
            printBody(actionDeclaration)
        }
        nl().keyword("END_ACTION")
    }

    override fun visit(invocation: InvocationStatement) = build {
        nl()
        accept(invocation.callee)
        visitInvocationParameter(invocation.parameters)
        +";"
    }

    override fun visit(aCase: Case) = build {
        nl()
        +aCase.conditions.flowMap(hardline) { accept(it) }
        +colon
        indent {
            +accept(aCase.statements)
        }
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) = build {
        +simpleTypeDeclaration.baseType.identifier!!
        /*if (simpleTypeDeclaration.initialization != null) {
            +(" := ")
            simpleTypeDeclaration.initialization!!accept()
        }*/
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) = build {
        +structureTypeDeclaration.name
        +": "
        keyword("STRUCT").nl()
        indent {
            structureTypeDeclaration.fields.forEach {
                nl()
                accept(it)
            }
        }
        keyword("END_STRUCT").write(";").nl()
    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration) = build {
        +subRangeTypeDeclaration.name
        +": "
        printf(subRangeTypeDeclaration.baseType.identifier!!)
        +"("
        accept(subRangeTypeDeclaration.range!!.start)
        +" .. "
        accept(subRangeTypeDeclaration.range!!.stop)
        +")"
        /*if (subRangeTypeDeclaration.initialization != null) {
            +(" := ")
            subRangeTypeDeclaration.initialization!!accept()
        }*/
        +";"
    }

    override fun visit(vd: VariableDeclaration) = build {
        write("${vd.name} :")
        variableDataType(vd)
    }

    val variableDeclarationUseDataType = false
    private fun variableDataType(vd: VariableDeclaration): Document {
        val dt = vd.dataType
        if (variableDeclarationUseDataType && dt != null) {
            return variableDataType(dt)
        } else {
            return accept(vd.typeDeclaration)
        }
    }

    fun variableDataType(dt: AnyDt) = string(dt.reprDecl())

    override fun visit(commentStatement: CommentStatement) = build {
        if (isPrintComments) {
            nl()
            if ('\n' in commentStatement.comment) {
                comment(literals.commentOpen() + commentStatement.comment + literals.commentClose())
            } else {
                comment("//%s\n", commentStatement.comment)
            }
        }
    }

    override fun visit(literal: Literal): Document {
        fun print(prefix: Any?, suffix: Any) = string((if (prefix != null) "$prefix#" else "") + suffix)
        return when (literal) {
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
                    string("\"${literal.value}\"")
                } else {
                    string("'${literal.value}'")
                }
            }

            is NullLit -> string("null")

            is TimeLit -> print(literal.dataType().name, "${literal.value.milliseconds}ms")

            is BooleanLit -> string(literal.value.toString().uppercase(Locale.getDefault()))

            is BitLit -> print(literal.dataType.obj?.name, "2#" + literal.value.toString(2))

            is UnindentifiedLit -> string(literal.value)
        }
    }

    override fun visit(arrayinit: ArrayInitialization) = lbracket +
        arrayinit.initValues.flowMap(commaSpace) { accept(it) } + rbracket

    override fun visit(localScope: Scope) = build {
        val variables = VariableScope(localScope.variables)
        variables.groupBy { it.type }
            .forEach { (type, v) ->
                val vars = v.toMutableList()
                vars.sortWith(compareBy { it.name })

                // By { a, b -> a.compareTo(b) }

                if (VariableDeclaration.INPUT and type >= VariableDeclaration.INOUT) {
                    nl().keyword("VAR_INOUT")
                } else {
                    when {
                        VariableDeclaration.INPUT and type != 0 -> keyword("VAR_INPUT")
                        VariableDeclaration.OUTPUT and type != 0 -> keyword("VAR_OUTPUT")
                        VariableDeclaration.EXTERNAL and type != 0 -> keyword("VAR_EXTERNAL")
                        VariableDeclaration.GLOBAL and type != 0 -> keyword("VAR_GLOBAL")
                        VariableDeclaration.TEMP and type != 0 -> keyword("VAR_TEMP")
                        else -> keyword("VAR")
                    }
                }
                space()
                if (VariableDeclaration.CONSTANT and type != 0) {
                    keyword("CONSTANT ")
                }
                if (VariableDeclaration.RETAIN and type != 0) {
                    keyword("RETAIN ")
                }
                space()
                indent {
                    for (vd in vars) {
                        print(vd)
                    }
                }
                nl().keyword("END_VAR")
                nl()
            }
    }

    open fun print(vd: VariableDeclaration) = build {
        nl()
        +vd.name
        +" : "
        variableDataType(vd)
        when {
            vd.initValue != null -> {
                +" := "
                val (dt, v) = vd.initValue as Value<*, *>
                +dt.repr(v)
            }

            vd.init != null -> {
                +" := "
                accept(vd.init)
            }
        }
        +";"
    }

    override fun visit(structureInitialization: StructureInitialization) =
        lparen +
            structureInitialization.initValues.entries.flowMap(commaSpace) { (t, v) ->
                string(t) + space + string(":=") + space + accept(v)
            } + rparen

    override fun visit(sfcStep: SFCStep) = build {
        nl()
        +if (sfcStep.isInitial) "INITIAL_STEP " else "STEP "
        +sfcStep.name
        printf(":")
        indent {
            sfcStep.events.forEach { aa -> visit(aa) }
        }
        nl()
        +"END_STEP"
        nl()
    }

    private fun visit(aa: SFCStep.AssociatedAction) = build {
        nl()
        printf(aa.actionName)
        +'('
        aa.qualifier?.let { q ->
            +q.qualifier.symbol
            if (q.qualifier.hasTime) {
                +", "
                +accept(q.time)
            }
        }
        +");"
    }

    override fun visit(sfcNetwork: SFCNetwork) = build {
        val seq = ArrayList(sfcNetwork.steps)
        seq.sortWith(compareBy(SFCStep::isInitial).thenBy(SFCStep::name))
        seq.forEach { a -> accept(a) }
        sfcNetwork.steps.stream()
            .flatMap { s -> s.incoming.stream() }
            .forEachOrdered { t -> accept(t) }
    }

    override fun visit(sfc: SFCImplementation) = build {
        // sfc.actions.forEach { a -> accept(a) }
        sfc.networks.forEach { n -> accept(n) }
    }

    override fun visit(transition: SFCTransition) = build {
        val f = transition.from.map { it.name }.reduce { a, b -> "$a, $b" }
        val t = transition.to.map { it.name }.reduce { a, b -> "$a, $b" }

        nl().keyword("TRANSITION").space().keyword("FROM").space()

        if (transition.from.size > 1) {
            +'('
            +f
            +')'
        } else {
            +f
        }
        space().keyword("TO").space()
        if (transition.to.size > 1) {
            +'('
            +t
            +')'
        } else {
            +t
        }
        +" := "

        accept(transition.guard)
        +";"
        space()
        keyword("END_TRANSITION")
    }

    private fun printBody(a: HasBody): Document {
        val stBody = a.stBody
        val sfcBody = a.sfcBody
        val ilBody = a.ilBody

        for (type in bodyPrintingOrder) {
            when (type) {
                BodyPrinting.ST if stBody != null -> return accept(stBody)
                BodyPrinting.SFC if sfcBody != null -> return accept(sfcBody)
                BodyPrinting.IL if ilBody != null -> return ilBody.accept(PPIlPrinter())
                else -> {}
            }
        }
        return empty
    }

    fun clear() {}

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

    override fun visit(jump: JumpStatement) = build {
        nl()
        +"JMP ${jump.target};"
    }

    override fun visit(label: LabelStatement) = build {
        nl()
        +"${label.label}:"
    }

    override fun visit(special: SpecialStatement) = build {
        val sep = comma + blank(1)

        when (special) {
            is SpecialStatement.Assert -> {
                nl()
                +"//# assert "
                special.name?.let { +": $it" }
                special.exprs.joinToDocument(sep) { accept(it) }
            }

            is SpecialStatement.Assume -> {
                nl()
                +"//# assume "
                special.name?.let { write(": $it") }
                special.exprs.joinToDocument(sep) { accept(it) }
            }

            is SpecialStatement.Havoc -> {
                nl()
                +"//# havoc "
                special.name?.let { write(": $it") }
                special.variables.joinToDocument(sep) { accept(it) }
            }
        }
    }
}