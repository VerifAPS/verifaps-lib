package edu.kit.iti.formal.automation.cpp

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.LookupList
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.SMVWordType
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto
import java.io.Writer
import java.util.*
import kotlin.collections.ArrayList

object TranslateToCppFacade {
    fun value(v: Value<*, *>?): String {
        return when (v) {
            null -> "/* null value */"
            is VBool -> v.value.toString()
            is VAnyBit -> "(${dataType(v.dataType)}) ${v.value}"
            is VAnyEnum -> "${v.dataType.name}_${v.value}"
            is VAnyInt -> "(${dataType(v.dataType)}) ${v.value}"
            is VStruct -> {
                "(struct ${v.dataType.name}_t)" +
                        v.fieldValues.joinToString(", ", "{", "}") { (n, v) ->
                            ".$n = ${value(v)}"
                        }
            }
            else -> "/* value $v unsupported */"
        }
    }

    fun dataType(any: AnyDt?): String {
        return when (any) {
            null -> "/* datatype is null */"
            VOID -> "void"
            is INT -> "int16_t"
            is SINT -> "int8_t"
            is LINT -> "int64_t"
            is DINT -> "int32_t"

            is UINT -> "uint16_t"
            is USINT -> "uint8_t"
            is ULINT -> "uint64_t"
            is UDINT -> "uint32_t"

            is AnyBit.BOOL -> "bool"
            is AnyBit.BYTE -> "uint8_t"
            is AnyBit.WORD -> "uint32_t"
            is AnyBit.DWORD -> "uint64_t"

            //TODO ranges * any.ranges.size)
            is ArrayType -> dataType(any.fieldType) + "[]"

            is IECString -> "const char*"
            is FunctionBlockDataType -> "struct ${any.functionBlock.name}_t"
            is EnumerateType -> "enum ${any.name}"
            is RecordType -> "struct " + any.name
            is PointerType -> dataType(any.of) + "*"
            is AnyReal.REAL -> "float"
            is AnyReal.LREAL -> "double"
            else -> "/* datatype: $any is not supported */"
        }
    }

    fun translate(writer: Writer, pous: PouElements) {
        val ttc = TranslateToCpp(CodeWriter(writer))
        pous.accept(ttc)
    }

    fun translate(op: UnaryOperator) = when (op) {
        Operators.NOT -> "!"
        else -> op.symbol
    }

    fun translate(op: BinaryOperator) = when (op) {
        Operators.NOT_EQUALS -> "!="
        Operators.AND -> "&&"
        Operators.OR -> "||"
        Operators.XOR -> "^"
        Operators.MOD -> "%"
        else -> op.symbol
    }

    fun translate(dataType: SMVType?): String {
        return when (dataType) {
            null -> "/* datatype is null */"
            is SMVTypes.INT -> "int"
            is SMVTypes.FLOAT -> "float"
            is SMVTypes.BOOLEAN -> "bool"
            is SMVWordType -> {
                (if (dataType.signed) "" else "u") +
                        when {
                            dataType.width >= 64 -> "long"
                            dataType.width >= 32 -> "int"
                            dataType.width >= 16 -> "short"
                            dataType.width >= 8 -> "byte"
                            else -> "int"
                        }
            }
            is EnumType -> "int"
            else -> "/* datatype: $dataType is not supported */"
        }
    }
}


/**
 *
 * @author Alexander Weigl
 * @version 1 (08.07.19)
 */
class TranslateToCpp(val out: CodeWriter) : AstVisitor<Unit>() {
    val translateToCppExpr = TranslateToCppExpr()

    override fun defaultVisit(obj: Any) {
        out.println("/* Unsupported $obj in $this */")
    }

    fun expr(e: Expression): String = e.accept(translateToCppExpr)
    fun exprN(e: Expression?): String? = e?.let { expr(it) }

    fun value(v: Value<*, *>?): String = TranslateToCppFacade.value(v)

    fun dataType(any: AnyDt?): String = TranslateToCppFacade.dataType(any)

    override fun visit(assignmentStatement: AssignmentStatement) {
        val lhs = expr(assignmentStatement.location)
        val rhs = expr(assignmentStatement.expression)
        out.nl().append("$lhs = $rhs;")
    }

    override fun visit(namespace: NamespaceDeclaration) {
        out.cblock("namespace ${namespace.fqName.name}", "}") {
            namespace.pous.accept(this@TranslateToCpp)
        }
    }

    //region case
    override fun visit(range: CaseCondition.Range) {
        val start = range.range.startValue
        val stop = range.range.stopValue
        for (i in start..stop) {
            out.nl().append("case $i:")
        }
    }

    override fun visit(integerCondition: CaseCondition.IntegerCondition) {
        out.nl().append("case ${expr(integerCondition.value)}:")
    }

    override fun visit(enumeration: CaseCondition.Enumeration) {
        val start = enumeration.start
        val stop = enumeration.stop
        val name = start.dataType.identifier!!

        if (stop == null) {
            out.nl().append("case ${expr(start)}:")
        } else {
            val range = start.dataType.obj!!.range(start.value, stop.value)
            for (i in range) {
                out.nl().append("case ${name}_$i:")
            }
        }
    }
    //endregion

    //region statements
    override fun visit(caseStatement: CaseStatement) {
        out.cblock("switch(${expr(caseStatement.expression)}) {", "}") {
            for (c in caseStatement.cases)
                c.accept(this@TranslateToCpp)

            if (caseStatement.elseCase.isNotEmpty()) {
                caseStatement.elseCase.also {
                    out.cblock("default:", "") {
                        it.accept(this@TranslateToCpp)
                    }
                }
            }
        }
    }

    override fun visit(repeatStatement: RepeatStatement) {
        out.cblock("do{", "} while(${expr(repeatStatement.condition)} ") {
            repeatStatement.statements.accept(this@TranslateToCpp)
        }
    }

    override fun visit(whileStatement: WhileStatement) {
        out.cblock("while(${expr(whileStatement.condition)} {", "}") {
            whileStatement.statements.accept(this@TranslateToCpp)
        }
    }

    override fun visit(forStatement: ForStatement) {
        val i = forStatement.variable
        val start = expr(forStatement.start)
        val stop = expr(forStatement.stop)
        val step = exprN(forStatement.step) ?: "1"

        out.cblock("for(int $i = $start; $i <= $stop; $i += $step ) {", "}") {
            forStatement.statements.accept(this@TranslateToCpp)
        }
    }

    override fun visit(ifStatement: IfStatement) {
        ifStatement.conditionalBranches.joinInto(out, " else ") {
            out.cblock("if (${expr(it.condition)}) {", "}") {
                it.statements.accept(this@TranslateToCpp)
            }
        }

        if (ifStatement.elseBranch.isNotEmpty()) {
            out.cblock("else {", "}") {
                ifStatement.elseBranch.accept(this@TranslateToCpp)
            }
        }

    }

    override fun visit(aCase: Case) {
        aCase.conditions.forEach { it.accept(this) }
        out.increaseIndent()
        aCase.statements.accept(this)
        out.nl().append("break;")
        out.decreaseIndent()
    }

    override fun visit(invocation: InvocationStatement) {
        val fbd = invocation.invoked as Invoked.FunctionBlock

        if (invocation.parameters.isNotEmpty())
            throw IllegalStateException()

        out.nl().append("${fbd.fb.name}(& ${expr(invocation.callee)});")
    }

    override fun visit(exitStatement: ExitStatement) {
        out.nl().print("break;")
    }

    override fun visit(returnStatement: ReturnStatement) {
        out.nl().print("return;")
    }

    override fun visit(commentStatement: CommentStatement) {
        out.nl().print("/* ${commentStatement.comment} */")
    }

    override fun visit(jump: JumpStatement) {
        out.nl().print("${jump.target}:")
    }

    override fun visit(label: LabelStatement) {
        out.nl().print("${label.label}:")
    }
    //endregion

    // decls
    override fun visit(functionDeclaration: FunctionDeclaration) {
        val rt = dataType(functionDeclaration.returnType.obj!!)
        val args = functionDeclaration.scope.variables.filter { it.isInput }
                .joinToString(", ") { "${dataType(it.dataType)} ${it.name}" }

        out.cblock("$rt ${functionDeclaration.name}($args) {", "}") {
            functionDeclaration.scope.variables
                    .filter { !it.isInput }
                    .forEach {
                        it.accept(this@TranslateToCpp)
                        out.print(";").nl()
                    }

            functionDeclaration.stBody?.accept(this@TranslateToCpp)

            nl().append("return ${functionDeclaration.name};")
        }
    }

    override fun visit(statements: StatementList) {
        traversalPolicy.traverse(statements)
    }

    lateinit var actionNamePrefix: String
    var currentStateVariable: String = "self"
    lateinit var currentStateType: String

    override fun visit(programDeclaration: ProgramDeclaration) {
        visit(programDeclaration as PouExecutable, programDeclaration.actions)
        val rt = RecordType(programDeclaration.name, programDeclaration.scope.variables)
        out.println("struct ${programDeclaration.name}_t ${programDeclaration.name.toUpperCase()} = ${value(DefaultInitValue.getInit(rt))};")
    }

    fun visit(pd: PouExecutable, actions: LookupList<ActionDeclaration>) {
        out.nl()
        currentStateType = "${pd.name}_t"
        actionNamePrefix = "${pd.name}_act_"

        generateScopeStruct(pd.scope, currentStateType)

        out.nl()
        translateToCppExpr.enableRewriteStateVariables(pd.scope, "$currentStateVariable->")

        out.cblock("void ${pd.name}(struct ${currentStateType}* $currentStateVariable) {", "}") {
            pd.stBody?.accept(this@TranslateToCpp)
        }

        if (actions.isNotEmpty()) {
            out.nl().append("//actions: ")
            actions.forEach { visit(actionNamePrefix, it) }
            out.nl().append("//end_actions")
        }
        translateToCppExpr.disableRewriteStateVariables()
    }

    private fun generateScopeStruct(scope: Scope, name: String) {
        val values = ArrayList<String>()
        out.cblock("struct $name {", "};") {
            scope.variables.forEach {
                out.print("${dataType(it.dataType)} ${it.name};")
                        .print("/* ${it.type.toString(2)} */")
                        .nl()
                values.add(value(it.initValue))
            }
        }
        //out.nl().print("const struct $name ${name}_default = {${values.joinToString(", ")}};\n")
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) = visit(functionBlockDeclaration as PouExecutable, functionBlockDeclaration.actions)

    fun visit(outer: String, action: ActionDeclaration) {
        out.cblock("void ${outer}_${action.name}(${outer}_state this) {", "}") {
            action.stBody?.accept(this@TranslateToCpp)
        }
    }

    override fun visit(variableDeclaration: VariableDeclaration) {
        val v = variableDeclaration.initValue
        if (v != null)
            out.print("${dataType(variableDeclaration.dataType)} ${variableDeclaration.name} = ${value(v)}")
        else
            out.print("${dataType(variableDeclaration.dataType)} ${variableDeclaration.name}")
    }

    override fun visit(elements: PouElements) {
        traversalPolicy.traverse(elements)
    }

    override fun visit(structureInitialization: StructureInitialization) {
        TODO()
    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration) {
        gvlDecl.scope.accept(this)
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        out.nl().cblock("struct ${structureTypeDeclaration.name} {", "}") {
            structureTypeDeclaration.fields.forEach {
                out.nl().append("${dataType(it.dataType)} ${it.name} = ${it.initValue}")
            }
        }
        super.visit(structureTypeDeclaration)
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        out.print("enum ${enumerationTypeDeclaration.name} {")
        val et = EnumerateType(enumerationTypeDeclaration)
        et.allowedValues.joinInto(out, ",\n") { t, u ->
            out.print("${enumerationTypeDeclaration.name}_$t = $u")
        }
        out.println("};")

    }
//endregion

    override fun visit(empty: EMPTY_EXPRESSION) {
        out.print("/* empty */")
    }

}

class TranslateToCppExpr : AstVisitor<String>() {
    private lateinit var statePrefix: String
    private lateinit var rewriteScope: Scope
    private var rewriteStateVariables: Boolean = false


    override fun defaultVisit(obj: Any) = "/* $obj not implemented in $this */"

    override fun visit(literal: Literal): String = when (literal) {
        is IntegerLit -> literal.value.toString()
        is StringLit -> '"' + literal.value + '"'
        is RealLit -> literal.value.toString()
        is EnumLit -> literal.dataType.identifier + '_' + literal.value
        is NullLit -> "NULL"
        is ToDLit -> TODO()
        is DateLit -> TODO()
        is TimeLit -> TODO()
        is DateAndTimeLit -> TODO()
        is BooleanLit -> literal.value.toString()
        is BitLit -> literal.value.toString()
        is UnindentifiedLit -> TODO()
    }

    override fun visit(binaryExpression: BinaryExpression): String {
        val left = binaryExpression.leftExpr.accept(this)
        val right = binaryExpression.rightExpr.accept(this)
        val op = TranslateToCppFacade.translate(binaryExpression.operator)
        return "($left $op $right)"
    }

    override fun visit(unaryExpression: UnaryExpression): String {
        val right = unaryExpression.expression.accept(this)
        val op = TranslateToCppFacade.translate(unaryExpression.operator)
        return "($op $right)"
    }

    override fun visit(symbolicReference: SymbolicReference): String {
        val sb = StringBuilder()

        if (rewriteStateVariables && rewriteScope.variables.contains(symbolicReference.identifier))
            sb.append(statePrefix + symbolicReference.identifier)
        else
            sb.append(symbolicReference.identifier)

        symbolicReference.subscripts?.forEach {
            sb.append("[").append(it.accept(this)).append("]")
        }

        if (symbolicReference.hasSub()) {
            val rw = rewriteStateVariables //rewrite only top level
            rewriteStateVariables = false
            sb.append(".").append(symbolicReference.sub?.accept(this))
            rewriteStateVariables = rw
        }

        return sb.toString()
    }

    override fun visit(invocation: Invocation): String {
        val args = invocation.inputParameters.joinToString(", ") { it.expression.accept(this) }
        return "${invocation.callee.accept(this)}($args)"
    }

    fun enableRewriteStateVariables(scope: Scope, statePrefix: String) {
        rewriteStateVariables = true
        rewriteScope = scope
        this.statePrefix = statePrefix
    }

    fun disableRewriteStateVariables() {
        rewriteStateVariables = false
    }
}

fun generateHeader(cw: CodeWriter) {
    cw.println("""
        //Generated on ${Date()}
    
        #include <stdint.h>
        #define NULL 0
        #define false 0 
        #define true 1

        typedef int bool;
    """.trimIndent())
}


fun generateRunnableStub(cw: CodeWriter, main: PouElements) {
    cw.nl()
    cw.cblock("int main(void) {", "}") {
        cw.cblock("while(true) {", "}") {
            main.elements.forEach { p ->
                if (p is ProgramDeclaration) {
                    val inputs = p.scope.filterByFlags(VariableDeclaration.INPUT, VariableDeclaration.INOUT)
                    inputs.forEach { print("havoc(&${p.name.toUpperCase()}.${it.name});").nl() }
                    print("${p.name}(& ${p.name.toUpperCase()});").nl()
                }
            }
        }
    }
}