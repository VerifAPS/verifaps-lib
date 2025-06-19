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
package edu.kit.iti.formal.automation.experimental

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.RecordValue
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.operators.Operator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.util.CodeWriter
import java.io.StringWriter
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.02.19)
 */
class JavaExportVisitor(val packageName: String, val rootClass: String) {
    val sw = StringWriter()
    val cw = CodeWriter(sw)

    fun export(pous: PouElements): String {
        cw.write("package $packageName;\n")
        cw.write("// Header").nl()
        cw.cblock("public class $rootClass {", "}") {
            val predicate: (PouElement) -> Boolean = { it is GlobalVariableListDeclaration }
            pous.filter(predicate)
                .map { it as HasScope }
                // TODO Make them static!
                .forEach { it.scope.accept(JavaExportVisitorImpl()) }

            pous.filter { it !is GlobalVariableListDeclaration }
                .forEach { it.accept(JavaExportVisitorImpl()) }

            cw.nl().cblock("public static void main(String[] args) {", "}") {
                pous.filter { it is ProgramDeclaration }
                    .forEach {
                        cw.nl().write("${it.name}.call();")
                    }
            }
        }
        return sw.toString()
    }

    fun iecToJavaType(dt: AnyDt): String = when (dt) {
        INT -> "short"
        SINT -> "byte"
        LINT -> "long"
        DINT -> "int"

        UINT -> "short"
        USINT -> "byte"
        ULINT -> "long"
        UDINT -> "int"

        AnyBit.BOOL -> "boolean"

        is FunctionBlockDataType -> dt.functionBlock.name
        is ClassDataType.ClassDt -> dt.clazz.name
        is ClassDataType.InterfaceDt -> dt.clazz.name
        is TimeType -> "long"
        is EnumerateType -> dt.name
        else -> throw IllegalStateException("$dt")
    }

    private inner class JavaExportVisitorImpl : AstVisitor<Unit>() {
        override fun defaultVisit(obj: Any) {}

        override fun visit(localScope: Scope) {
            localScope.variables.forEach {
                cw.nl().write(variableDecl(it))
            }
        }

        override fun visit(programDeclaration: ProgramDeclaration) {
            val name = programDeclaration.name
            cw.nl().cblock("public static class $name {", "}") {
                visit(programDeclaration.scope)
                cw.cblock("public void call() {", "}") {
                    programDeclaration.stBody?.also { translateSt(it, programDeclaration.scope) }
                }
            }
            cw.nl().write("static $name $name = new $name();").nl()
        }

        override fun visit(functionDeclaration: FunctionDeclaration) {
            val rt = iecToJavaType(functionDeclaration.returnType.obj!!)

            val inp = functionDeclaration.scope.filter { it.isInput }
                .joinToString(", ") { iecToJavaType(it.dataType!!) + " " + it.name }

            val initOut = functionDeclaration.returnType

            cw.nl().cblock("public $rt  ${functionDeclaration.name}($inp) {", "}") {
                functionDeclaration.scope.filter { !it.isInput }
                    .forEach {
                        cw.write(variableDecl(it)).nl()
                    }
                functionDeclaration.stBody?.also { translateSt(it, functionDeclaration.scope) }
                cw.nl().write("return ${functionDeclaration.name};")
            }
        }

        override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
            cw.nl().cblock("public static class ${functionBlockDeclaration.name} {", "}") {
                val scope = functionBlockDeclaration.scope.sortedBy { it.name }
                visit(functionBlockDeclaration.scope) // vars are global
                val ctorArgs = scope.joinToString { iecToJavaType(it.dataType!!) + "  " + it.name }
                cw.nl().cblock("public ${functionBlockDeclaration.name}($ctorArgs) {", "}") {
                    scope.forEach {
                        val name = it.name
                        cw.nl().write("this.$name = $name;")
                    }
                }

                cw.nl().cblock("public void call() {", "}") {
                    functionBlockDeclaration.stBody?.also { translateSt(it, functionBlockDeclaration.scope) }
                }
            }
        }

        override fun visit(clazz: ClassDeclaration) {
            cw.cblock("public static class ${clazz.name} {", "}") {
                visit(clazz.scope)
                clazz.methods.forEach { it.accept(this@JavaExportVisitorImpl) }
            }
        }

        override fun visit(interfaceDeclaration: InterfaceDeclaration) {
            cw.nl().cblock("public interface ${interfaceDeclaration.name} {", "}") {
                interfaceDeclaration.methods.forEach { it.accept(this@JavaExportVisitorImpl) }
            }
        }

        override fun visit(method: MethodDeclaration) {
            val rt = iecToJavaType(method.returnType.obj!!)

            val inp = method.scope.filter { it.isInput }
                .joinToString(", ") { iecToJavaType(it.dataType!!) + " " + it.name }

            val initOut = method.returnType

            cw.cblock("public $rt  ${method.name}($inp) {", "}") {
                method.scope.filter { !it.isInput }
                    .forEach {
                        cw.write(variableDecl(it)).nl()
                    }
                method.stBody?.also { translateSt(it, method.scope) }
                cw.nl().write("return ${method.name};")
            }
        }

        override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
            cw.nl().cblock("public enum ${enumerationTypeDeclaration.name} {", "}") {
                val v = enumerationTypeDeclaration.allowedValues
                    .joinToString(", ", "", ";") { it.text.uppercase(Locale.getDefault()) }
                cw.write(v)
            }
            cw.nl()
        }
    }

    private fun translateValue(x: Value<*, *>): String {
        val (dt, v) = x
        if (dt is EnumerateType) return "${dt.name}.$v"
        return when (v) {
            is RecordValue -> {
                val dt = dt as RecordType
                val args = v.fieldValues.keys.sorted().joinToString {
                    val a = v.fieldValues[it]!!
                    "(${iecToJavaType(a.dataType)}) " + translateValue(a)
                }
                "new ${dt.name}($args)"
            }
            is TimeData -> v.milliseconds.toString() + "/* milliseconds */"
            else -> v.toString()
        }
    }

    private fun variableDecl(vd: VariableDeclaration): String {
        val dt = iecToJavaType(vd.dataType!!)
        return vd.initValue?.let {
            val init = translateValue(it)
            "$dt ${vd.name} = $init;"
        } ?: "$dt ${vd.name};"
    }

    private fun translateSt(list: StatementList, scope: Scope) {
        list.accept(JavaExportStmtImpl(scope))
    }

    private inner class JavaExportStmtImpl(val scope: Scope) : AstVisitor<Unit>() {
        override fun defaultVisit(obj: Any) {
            cw.write("// Unsupported statement ${obj.javaClass}").nl()
        }

        override fun visit(ifStatement: IfStatement) {
            cw.nl()
            ifStatement.conditionalBranches.forEach {
                val cond = translateExpr(it.condition)
                cw.cblock("if($cond) {", "}") {
                    it.statements.accept(this@JavaExportStmtImpl)
                }
            }

            if (ifStatement.elseBranch.isNotEmpty()) {
                cw.cblock("else {", "}") {
                    ifStatement.elseBranch.accept(this@JavaExportStmtImpl)
                }
            }
        }

        override fun visit(assignmentStatement: AssignmentStatement) {
            val lhs = translateExpr(assignmentStatement.location)
            val rhs = translateExpr(assignmentStatement.expression)

            val cast = try {
                val expdt = assignmentStatement.location.dataType(scope)
                val gotdt = assignmentStatement.location.dataType(scope)
                /*if (gotdt == expdt) ""
                else*/
                "(${iecToJavaType(expdt)})"
            } catch (e: Exception) {
                "/* no cast found ${e.message}*/"
            }

            cw.nl().write("$lhs = $cast $rhs;")
        }

        override fun visit(caseStatement: CaseStatement) {
            cw.nl()
            val expr = translateExpr(caseStatement.expression)
            cw.cblock("switch($expr) {", "}") {
                caseStatement.cases.forEach { it.accept(this@JavaExportStmtImpl) }
                caseStatement.elseCase?.let {
                    nl().cblock("default: {", "}") {
                        it.accept(this@JavaExportStmtImpl)
                    }
                }
            }
        }

        override fun visit(aCase: Case) {
            aCase.conditions.forEach { it.accept(this) }
            cw.increaseIndent().nl()
            aCase.statements.accept(this)
            cw.nl().write("break;").decreaseIndent().nl()
        }

        override fun visit(range: CaseCondition.Range) {
            (range.range.startValue..range.range.stopValue).forEach {
                cw.nl().write("case $it:")
            }
        }

        override fun visit(integerCondition: CaseCondition.IntegerCondition) {
            cw.nl().write("case ${translateExpr(integerCondition.value)}:")
        }

        override fun visit(enumeration: CaseCondition.Enumeration) {
            val n = (enumeration.start).value.uppercase(Locale.getDefault())
            cw.nl().write("case $n:")
        }

        override fun visit(exitStatement: ExitStatement) {
            cw.nl().write("break;")
        }

        override fun visit(commentStatement: CommentStatement) {
            cw.nl().write("// ${commentStatement.comment}")
        }

        override fun visit(returnStatement: ReturnStatement) {
            cw.nl().write("return;")
        }

        override fun visit(invocation: InvocationStatement) {
            val c = translateExpr(invocation.callee)
            invocation.inputParameters.forEach {
                val sr = invocation.callee.copy(sub = SymbolicReference(it.name))
                val t = AssignmentStatement(sr, it.expression)
                t.accept(this)
            }
            cw.nl().write("$c.call();").nl()
            invocation.outputParameters.forEach {
                val sr = it.expression as SymbolicReference
                val t = AssignmentStatement(
                    sr,
                    invocation.callee.copy(sub = SymbolicReference(it.name)),
                )
                t.accept(this)
            }
        }

        override fun visit(forStatement: ForStatement) {
            val start = translateExpr(forStatement.start)
            val stop = translateExpr(forStatement.stop)
            val step = forStatement.step?.let { translateExpr(it) } ?: "0"
            val v = forStatement.variable

            cw.cblock("for(int $v=$start; $v<=$stop; $v+=$step) {", "}") {
                forStatement.statements.accept(this@JavaExportStmtImpl)
            }
        }

        override fun visit(whileStatement: WhileStatement) {
            val cond = translateExpr(whileStatement.condition)
            cw.cblock("while($cond) {", "}") {
                whileStatement.statements.accept(this@JavaExportStmtImpl)
            }
        }

        override fun visit(repeatStatement: RepeatStatement) {
            val cond = translateExpr(repeatStatement.condition)
            cw.cblock("do {", "} while(($cond);") {
                repeatStatement.statements.accept(this@JavaExportStmtImpl)
            }
        }

        override fun visit(statements: StatementList) {
            statements.forEach { it.accept(this) }
        }
    }

    private fun translateExpr(expression: Expression): String = expression.accept(JavaExportExprImpl)

    object JavaExportExprImpl : AstVisitorWithScope<String>() {
        override fun defaultVisit(obj: Any) = "/* Unsupported construct: $obj */"

        override fun visit(unaryExpression: UnaryExpression): String = translateOp(unaryExpression.operator) +
            "(" + unaryExpression.expression.accept(this) + ")"

        private fun translateOp(operator: Operator): String = when (operator) {
            Operators.ADD -> "+"
            Operators.AND -> "&&"
            Operators.MINUS -> "-"
            Operators.DIV -> "/"
            Operators.EQUALS -> "=="
            Operators.NOT_EQUALS -> "!="
            Operators.LESS_EQUALS -> "<="
            Operators.LESS_THAN -> "<"
            Operators.GREATER_EQUALS -> ">="
            Operators.GREATER_THAN -> ">"
            Operators.MULT -> "*"
            Operators.OR -> "||"
            Operators.POWER -> throw java.lang.IllegalStateException("power not supported yet")
            Operators.SUB -> "-"
            Operators.NOT -> "!"
            else -> operator.toString()
        }

        override fun visit(symbolicReference: SymbolicReference): String {
            val array = (
                if (symbolicReference.isArrayAccess) {
                    "[" + symbolicReference.subscripts?.accept(this) + "]"
                } else {
                    ""
                }
                )
            val sub = symbolicReference.sub?.let { "." + it.accept(this) } ?: ""
            return symbolicReference.identifier + array + sub
        }

        override fun visit(binaryExpression: BinaryExpression): String = (
            "(" + binaryExpression.leftExpr.accept(this) + " " +
                translateOp(binaryExpression.operator) + " " +
                binaryExpression.rightExpr.accept(this) + ")"
            )

        override fun visit(expressions: ExpressionList): String = expressions.joinToString(", ") { it.accept(this) }

        override fun visit(invocation: Invocation): String = invocation.callee.accept(this) + "(" +
            invocation.parameters.joinToString(", ") { it.expression.accept(this) } + ")"

        override fun visit(literal: Literal): String {
            val td = literal.asValue()?.value
            return when (literal) {
                is TimeLit -> {
                    val a: TimeData = td as TimeData
                    a.milliseconds.toString()
                }
                is EnumLit -> {
                    literal.dataType.identifier!! + "." + literal.value.uppercase(Locale.getDefault())
                }
                else -> td?.toString() ?: ""
            }
        }
    }
}