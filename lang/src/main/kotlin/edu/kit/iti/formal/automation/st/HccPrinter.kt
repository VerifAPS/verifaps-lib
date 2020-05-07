package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.il.IlPrinter
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto
import edu.kit.iti.formal.util.meta

open class HccPrinter(sb: CodeWriter = CodeWriter(), noPreamble: Boolean = false) : StructuredTextPrinter(sb) {
    init {
        if (!noPreamble) {
            sb.print("""
                int nondet_int() { int i; return i; }
                int nondet_bool() { return nondet_int()?0:1; }
                int nondet_enum() { return nondet_int(); }
            """.trimIndent())
        }
    }

    override fun visit(empty: EMPTY_EXPRESSION) {
        sb.print("/* empty expression */")
    }

//    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {}

    override fun visit(stringTypeDeclaration: StringTypeDeclaration) {
        sb.printf("string")
    }

    override fun visit(exitStatement: ExitStatement) {
        sb.printf("break;")

    }

    override fun visit(binaryExpression: BinaryExpression) {
        if (binaryExpression.operator == Operators.POWER) {
            sb.printf("pow( ")
            binaryExpression.leftExpr.accept(this)
            sb.printf(", ")
            binaryExpression.rightExpr.accept(this)
            sb.append(')')
        } else {
            sb.append('(')
            binaryExpression.leftExpr.accept(this)
            when (binaryExpression.operator) {
                Operators.MOD -> sb.printf(" % ")
                Operators.AND -> sb.printf(" && ")
                Operators.OR -> sb.printf(" || ")
                Operators.XOR -> sb.printf(" ^ ")
                Operators.EQUALS -> sb.printf(" == ")
                Operators.NOT_EQUALS -> sb.printf(" != ")
                else -> sb.printf(" ${binaryExpression.operator.symbol} ")
            }
            binaryExpression.rightExpr.accept(this)
            sb.append(')')
        }
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        sb.nl()
        assignmentStatement.location.accept(this)
        if (assignmentStatement.isAssignmentAttempt)
            sb.printf(" = ")
        else
            sb.printf(" = ")
        assignmentStatement.expression.accept(this)
        sb.printf(";")
    }

    override fun visit(init: IdentifierInitializer) {
        sb.printf("THERE").printf(init.value!!)

    }

    override fun visit(repeatStatement: RepeatStatement) {
        sb.nl()
        sb.printf("do {").increaseIndent()
        repeatStatement.statements.accept(this)

        sb.decreaseIndent().nl().printf("} while ( ")
        repeatStatement.condition.accept(this)
        sb.printf(" )")

    }

    override fun visit(whileStatement: WhileStatement) {
        sb.nl()
        sb.printf("while( ")
        whileStatement.condition.accept(this)
        sb.printf(" ) {").increaseIndent()
        whileStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("}")
    }

    override fun visit(unaryExpression: UnaryExpression) {
        when (unaryExpression.operator) {
            Operators.NOT -> sb.printf("!")
            else -> sb.printf(unaryExpression.operator.symbol)
        }
        unaryExpression.expression.accept(this)

    }


    override fun visit(caseStatement: CaseStatement) {

        sb.nl().printf("switch( ")
        caseStatement.expression.accept(this)
        sb.printf(" )").increaseIndent().nl().printf("{").nl()

        for (c in caseStatement.cases) {
            c.accept(this)
            sb.nl() //TODO "break;" ?
        }

        if (caseStatement.elseCase.size > 0) {
            sb.nl().printf("default: ")
            caseStatement.elseCase.accept(this)
        }

        sb.nl().decreaseIndent().appendIdent().printf("}")

    }


    override fun visit(programDeclaration: ProgramDeclaration) {
        printComment(programDeclaration.comment)
        sb.printf("/* program  ").printf(programDeclaration.name).printf(" */").nl()
        sb.printf("void main(void) {").increaseIndent()
        programDeclaration.scope.accept(this)

        sb.nl()

        if (!programDeclaration.actions.isEmpty()) {
            programDeclaration.actions.forEach { v -> v.accept(this) }
            sb.nl()
        }

        printBody(programDeclaration)

        sb.decreaseIndent().nl().printf("}").nl().printf("/* end program */").nl()
    }


    override fun visit(forStatement: ForStatement) {
        sb.nl()
        sb.printf("for( int ").printf(forStatement.variable)
        sb.printf(" = ")
        forStatement.start.accept(this)
        sb.printf("; ").printf(forStatement.variable)
        sb.printf(" < ")
        forStatement.stop.accept(this)
        sb.printf("; ").printf(forStatement.variable).printf("++) {").increaseIndent()
        forStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("}")

    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        printComment(functionDeclaration.comment)
        sb.printf("/* function ").printf(functionDeclaration.name).printf(" */").nl()

        val returnType = functionDeclaration.returnType.identifier
        if (!(returnType == null || returnType.isEmpty()))
            sb.printf(returnType.toLowerCase()).printf(" ${functionDeclaration.name}( ")
        functionDeclaration.scope.variables.filter { it.isInput || it.isInOut }.forEachIndexed { i, it ->
            if (i != 0) {
                sb.printf(", ")
            }
            variableDataType(it)
            sb.printf(" ").printf(it.name)
        }
        sb.printf(" ) {").increaseIndent().nl()


        val scopeWithoutInput = Scope(functionDeclaration.scope.variables.filter { !it.isInput && !it.isInOut })

        scopeWithoutInput.accept(this)


        printBody(functionDeclaration)


        val outVars = functionDeclaration.scope.variables.filter { it.isOutput || it.isInOut }
        if (outVars.isNotEmpty())
            sb.nl().printf("return ${outVars.first().name};")


        sb.decreaseIndent().nl().printf("}").nl().printf("/* end function */").nl().nl()

    }

    override fun visit(returnStatement: ReturnStatement) {
        sb.nl().printf("return;")
    }

    override fun visit(ifStatement: IfStatement) {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            sb.nl()

            if (i == 0)
                sb.printf("if( ")
            else
                sb.printf("} else if( ")

            ifStatement.conditionalBranches[i].condition.accept(this)

            sb.printf(" ) {").increaseIndent()
            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.decreaseIndent()

        }

        if (ifStatement.elseBranch.size > 0) {
            sb.nl().printf("} else {").increaseIndent()
            ifStatement.elseBranch.accept(this)
            sb.decreaseIndent()
        }
        sb.nl().printf("}")

    }

//    override fun visit(actionDeclaration: ActionDeclaration) {}

    override fun visit(aCase: Case) {
        sb.nl()
        sb.printf("case ")
        aCase.conditions.joinInto(sb) { it.accept(this) }
        sb.printf(":")
        sb.block() {
            aCase.statements.accept(this@HccPrinter)
        }
    }


    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        if (simpleTypeDeclaration.baseType.obj is AnyBit.BOOL) {
            sb.printf("int")
        } else if (simpleTypeDeclaration.baseType.obj is EnumerateType) {
            sb.printf("int")
        } else if (simpleTypeDeclaration.baseType.obj is UINT) {
            sb.printf("unsigned int")
        } else {
            sb.printf(simpleTypeDeclaration.baseType.identifier!!.toLowerCase())

        }

    }

//    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {}
//    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration) {}


    override fun visit(commentStatement: CommentStatement) {
        if (isPrintComments) {
            sb.nl()
            sb.printf("/* ")
            sb.printf(commentStatement.comment)
            sb.printf(" */")
        }
        val meta: SpecialCommentMeta? = commentStatement.meta<SpecialCommentMeta>()
        when (meta) {
            is SpecialCommentMeta.AssertComment -> {
                sb.nl()
                sb.printf("assert( ")
                meta.expr.accept(this)
                sb.printf(" );")
            }
            is SpecialCommentMeta.AssumeComment -> {
                sb.nl()
                sb.printf("assume( ")
                meta.expr.accept(this)
                sb.printf(" );")
            }
            is SpecialCommentMeta.HavocComment -> {
                sb.nl()
                val haveocName = "nondet_${meta.dataType.name.toLowerCase()}();"
                //sb.printf(" ").printf(haveocName).printf(" = _;").nl() //uninitialised Var
                sb.printf(meta.variable).printf(" = ").printf(haveocName)
            }
        }
    }

    override fun visit(literal: Literal) {
        fun print(prefix: Any?, suffix: Any) = "$suffix"
//                (if (prefix != null) "$prefix#" else "") + suffix

        sb.printf(when (literal) {
            is IntegerLit -> print(literal.dataType.obj?.name, literal.value.abs())
            is RealLit -> print(literal.dataType.obj?.name, literal.value.abs())
            //TODO maybe print the integer value
            is EnumLit -> ("${literal.dataType.obj?.name}__${literal.value}")
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
                if (literal.dataType() is IECString.WSTRING) "\"${literal.value}\""
                else "'${literal.value}'"
            }
            is NullLit -> "null"
            is TimeLit -> {
                print(literal.dataType().name, "${literal.value.milliseconds}ms")
            }
            is BooleanLit -> {
                if (literal == BooleanLit.LTRUE) {
                    "1"
                } else {
                    "0"
                }
            }
            is BitLit -> {
                print(literal.dataType.obj?.name, "2#" + literal.value.toString(2))
            }
            is UnindentifiedLit -> literal.value
        })
    }

    override fun visit(localScope: Scope) {
        if (localScope.topLevel != localScope)
            visitVariables(localScope.topLevel.variables)
        val variables = VariableScope(localScope.variables)
        visitVariables(variables)
    }

    private fun visitVariables(variables: VariableScope) {
        variables.groupBy { it.type }
                .forEach { (type, v) ->
                    val vars = v.toMutableList()
                    vars.sortWith(compareBy { it.name })

                    //By { a, b -> a.compareTo(b) }
                    sb.nl().printf("/* VAR")

                    if (VariableDeclaration.INPUT and type >= VariableDeclaration.INOUT) {
                        sb.printf("_INOUT")
                    } else {
                        when {
                            VariableDeclaration.INPUT and type != 0 -> sb.printf("_INPUT")
                            VariableDeclaration.OUTPUT and type != 0 -> sb.printf("_OUTPUT")
                            VariableDeclaration.EXTERNAL and type != 0 -> sb.printf("_EXTERNAL")
                            VariableDeclaration.GLOBAL and type != 0 -> sb.printf("_GLOBAL")
                            VariableDeclaration.TEMP and type != 0 -> sb.printf("_TEMP")
                        }
                    }
                    sb.printf(" ")
                    if (VariableDeclaration.CONSTANT and type != 0)
                        sb.printf("CONSTANT ")
                    if (VariableDeclaration.RETAIN and type != 0)
                        sb.printf("RETAIN ")
                    sb.printf("*/")
                    //sb.printf(type)

                    sb.increaseIndent()
                    for (vd in vars) {
                        print(vd)
                    }
                    sb.decreaseIndent().nl().printf("/* END_VAR */")
                    sb.nl()
                }
    }

    override fun print(vd: VariableDeclaration) {
        sb.nl()
        variableDataType(vd)
        if (vd.dataType != null) {
            var vdspec = vd.dataType!!.name
        }
        sb.printf(" ").printf(vd.name)

        when {
            vd.initValue != null -> {
                sb.printf(" = ")
                val (dt, v) = vd.initValue as Value<*, *>

                when (dt) {
                    is AnyBit.BOOL -> {
                        if (v == true) {
                            sb.printf("1")
                        } else if (v == false) {
                            sb.printf("0")
                        }
                    }
                    is EnumerateType -> {
                        sb.printf("${dt.name}__${v}")


                    }
                    else -> sb.printf(v.toString())
                }
            }
            vd.init != null -> {
                sb.printf(" = ")
                vd.init!!.accept(this)
            }
        }
        sb.printf(";")
    }

    //copied
    private fun variableDataType(vd: VariableDeclaration) {
        val dt = vd.dataType
        if (variableDeclarationUseDataType && dt != null) {
            variableDataType(dt)
        } else {
            vd.typeDeclaration?.accept(this)
        }
    }

    override fun visit(jump: JumpStatement) {
        sb.nl().write("goto ${jump.target};")
    }


// private functions

    //copied
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

    //adapted
    private fun printComment(comment: String) {
        if (comment.isNotBlank()) {
            sb.printf("/*")
            sb.printf(comment)
            sb.printf("*/").nl()
        }
    }


}

object SpecialCommentFactory {
    fun createHavoc(name: String, dt: AnyDt): CommentStatement {
        val comment = CommentStatement("havoc $name")
        comment.meta<SpecialCommentMeta>(SpecialCommentMeta.HavocComment(name, dt))
        return comment
    }

    fun createAssume(expression: Expression): CommentStatement {
        val comment = CommentStatement("assumption of constraints")
        comment.meta<SpecialCommentMeta>(SpecialCommentMeta.AssumeComment(expression))
        return comment
    }

    fun createAssert(expression: Expression): Statement {
        val comment = CommentStatement("assert")
        comment.meta<SpecialCommentMeta>(SpecialCommentMeta.AssertComment(expression))
        return comment
    }
}

sealed class SpecialCommentMeta {
    class AssertComment(var expr: Expression) : SpecialCommentMeta()
    class AssumeComment(var expr: Expression) : SpecialCommentMeta()
    class HavocComment(var variable: String, val dataType: AnyDt) : SpecialCommentMeta()
}