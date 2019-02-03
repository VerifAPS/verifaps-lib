package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.util.*
import edu.kit.iti.formal.util.SemanticClasses.*
import java.io.Writer


/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
/*open class StructuredTextHtmlPrinter(stream: Writer) : DefaultVisitor<Unit>() {
    private var sb = SemanticCodeWriter(DefaultHtmlSemantic(), stream)
    var isPrintComments: Boolean = false

    override fun defaultVisit(obj: Any) {
        sb.cliFormat(SemanticClasses.ERROR, "not implemented: ")
                .cliFormat(obj::class.java)
    }

    override fun visit(exitStatement: ExitStatement) {
        sb.cliFormat(STATEMENT, KEYWORD, "EXIT").cliFormat(";")
    }


    override fun visit(integerCondition: CaseCondition.IntegerCondition) {
        sb.open(CASE_INTEGER_CONDITION)
        integerCondition.value.accept(this)
        sb.close()
    }


    override fun visit(enumeration: CaseCondition.Enumeration) {
        sb.cliFormat(CASE_ENUM_CONDITION)
        if (enumeration.start === enumeration.stop) {
            sb.appendIdent()
            enumeration.start.accept(this)
        } else {
            sb.appendIdent()
            enumeration.start.accept(this)
            sb.printf("..")
            enumeration.stop!!.accept(this)
        }
        sb.close()

    }


    override fun visit(binaryExpression: BinaryExpression) {
        sb.cliFormat(BINARY_EXPRESSION)
        sb.append('(')
        binaryExpression.leftExpr.accept(this)
        sb.cliFormat(OPERATOR, KEYWORD)
        sb.printf(" ").printf(binaryExpression.operator!!.symbol).printf(" ")
        sb.close().close()
        binaryExpression.rightExpr.accept(this)
        sb.append(')')
        sb.close()

    }


    override fun visit(assignStatement: AssignmentStatement) {
        sb.semblock(ASSIGNMENT) {
            assignStatement.location.accept(this)
            sb.cliFormat(OPERATOR, ":=")
            assignStatement.expression.accept(this)
        }
        sb.cliFormat(OPERATOR, ";")
    }


    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        sb.cliFormat(TYPE_DECL_ENUM).cliFormat(TYPE_NAME).printf(enumerationTypeDeclaration.name)
        sb.close().seperator(":")

        sb.cliFormat(TYPE_DECL_DECL).printf("(")

        for (s in enumerationTypeDeclaration.allowedValues) {
            sb.cliFormat(VALUE).printf(s.text)
            sb.close().seperator(",")
        }

        sb.printf(")")
        sb.ts().close().close()
    }


    override fun visit(repeatStatement: RepeatStatement) {
        sb.cliFormat(REPEAT).keyword("REPEAT")
        repeatStatement.statements.accept(this)
        sb.keyword(" UNTIL ")
        repeatStatement.condition.accept(this)
        sb.keyword("END_REPEAT")
        sb.close()

    }


    override fun visit(whileStatement: WhileStatement) {
        sb.cliFormat(WHILE).keyword("WHILE")
        whileStatement.condition.accept(this)
        sb.keyword(" DO ")
        whileStatement.statements.accept(this)
        sb.keyword("END_WHILE")
        sb.close()

    }


    override fun visit(unaryExpression: UnaryExpression) {
        sb.cliFormat(UNARY_EXPRESSION, OPERATOR)
                .printf(unaryExpression.operator.symbol)
        sb.close().printf(" ")
        unaryExpression.expression.accept(this)
        sb.close()

    }


    override fun visit(typeDeclarations: TypeDeclarations) {
        sb.cliFormat(TYPE_DECL).keyword("TYPE")
        for (decl in typeDeclarations) {
            decl.accept(this)
        }
        sb.keyword("END_TYPE")
        sb.close()

    }


    override fun visit(caseStatement: CaseStatement) {
        sb.cliFormat(CASE_STATEMENT).keyword("CASE")
        caseStatement.expression!!.accept(this)
        sb.keyword(" OF ")
        for (c in caseStatement.cases) {
            c.accept(this)
        }
        sb.keyword("END_CASE")
        sb.close()

    }


    override fun visit(symbolicReference: Location) {
        /*TODO
        sb.variable(symbolicReference.getName());


		if (symbolicReference.getSubscripts() != null && !symbolicReference.getSubscripts().isEmpty()) {

			sb.cliFormat(SUBSCRIPT).printf('[');
			for (Expression expr : symbolicReference.getSubscripts()) {
				expr.accept(this);
				sb.printf(',');
			}
			sb.printf(']');
			sb.close();
		}

		if (symbolicReference.getSub() != null) {
			sb.printf(".");
			symbolicReference.getSub().accept(this);
		}*/

    }


    override fun visit(statements: StatementList) {
        sb.cliFormat(STATEMENT_BLOCK)
        for (stmt in statements) {
            if (stmt == null) {
                sb.printf("{*ERROR: stmt null*}")
            } else {
                sb.cliFormat(STATEMENT)
                stmt.accept(this)
                sb.close()
            }
        }
        sb.close()

    }


    override fun visit(programDeclaration: ProgramDeclaration) {
        sb.cliFormat(PROGRAM).keyword("PROGRAM")
        sb.cliFormat(VARIABLE).printf(programDeclaration.name)
        sb.close().append('\n')

        programDeclaration.scope.accept(this)

        programDeclaration.stBody!!.accept(this)
        sb.keyword("END_PROGRAM")
        sb.close()

    }

    /**
     * {@inheritDoc}
     *
     * @Override public Object visit(ScalarValue tsScalarValue) {
     * sb.cliFormat(VALUE).span(tsScalarValue.getDataType().getName())
     * .printf(tsScalarValue.getDataType().repr(tsScalarValue.getValue()));
     * sb.close().close();
     * ;
     * }
     */


    override fun visit(expressions: ExpressionList) {
        sb.cliFormat(EXPRESSION_LIST)
        for (e in expressions) {
            e.accept(this)
            sb.seperator(",")
        }//TODO
        sb.close()

    }


    override fun visit(invocation: Invocation) {
        sb.cliFormat(FUNC_CALL)
        sb.printf(invocation.calleeName)
        visitInvocationParameters(invocation.parameters)

    }

    private fun visitInvocationParameters(parameters: MutableList<InvocationParameter>) {
        sb.printf("(")
        parameters.joinInto(sb, ",") { it.accept(this) }
        sb.printf(")")
    }


    override fun visit(forStatement: ForStatement) {
        sb.cliFormat(FOR)
        sb.keyword("FOR")
        sb.variable(forStatement.variable!!)
        sb.printf(" := ")
        forStatement.start!!.accept(this)
        sb.keyword("TO")
        forStatement.stop!!.accept(this)
        sb.keyword("DO")
        forStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("END_FOR")
        sb.close()

    }


    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        sb.cliFormat(FB).keyword("FUNCTION_BLOCK ").variable(functionBlockDeclaration.name)

        functionBlockDeclaration.scope.accept(this)

        functionBlockDeclaration.stBody!!.accept(this)
        sb.keyword("END_FUNCTION_BLOCK").ts().close()

    }


    override fun visit(returnStatement: ReturnStatement) {
        sb.keyword("RETURN").ts()

    }


    override fun visit(ifStatement: IfStatement) {
        sb.cliFormat(IFSTATEMENT)

        for (i in 0 until ifStatement.conditionalBranches.size) {
            if (i == 0)
                sb.keyword("IF")
            else
                sb.keyword("ELSIF")

            ifStatement.conditionalBranches[i].condition.accept(this)
            sb.keyword("THEN")
            sb.cliFormat("thenblock")
            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.close()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.keyword("ELSE")
            ifStatement.elseBranch.accept(this)
        }
        sb.keyword("END_IF").ts().close()

    }


    override fun visit(fbc: InvocationStatement) {
        fbc.callee.accept(this)
        visitInvocationParameters(fbc.parameters)
        sb.printf(";")
    }


    override fun visit(aCase: Case) {
        sb.cliFormat(CASE)
        for (cc in aCase.conditions) {
            cc.accept(this)
            sb.seperator(",")
        }
        //TODO
        sb.seperator(":")

        aCase.statements.accept(this)
        sb.close()

    }


    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        sb.cliFormat(TYPE_DECL_SIMPLE).type(simpleTypeDeclaration.baseType.identifier)
        if (simpleTypeDeclaration.initialization != null) {
            sb.operator(" := ")
            simpleTypeDeclaration.initialization!!.accept(this)
        }
        sb.close()

    }


    override fun visit(localScope: Scope) {
        sb.cliFormat(VARIABLES_DEFINITIONS)
        for (vd in localScope.variables) {
            sb.cliFormat(VARIABLES_DEFINITION)

            if (vd.isInput)
                sb.keyword("VAR_INPUT")
            else if (vd.isOutput)
                sb.keyword("VAR_OUTPUT")
            else if (vd.isInOut)
                sb.keyword("VAR_INOUT")
            else if (vd.isExternal)
                sb.keyword("VAR_EXTERNAL")
            else if (vd.isGlobal)
                sb.keyword("VAR_GLOBAL")
            else
                sb.keyword("VAR")

            if (vd.isConstant)
                sb.keyword("CONSTANT")

            if (vd.isRetain)
                sb.keyword("RETAIN")
            else
                sb.keyword("NON_RETAIN")

            sb.printf(" ")

            sb.variable(vd.name)

            sb.seperator(":")
            sb.type(vd.dataType?.name)

            if (vd.init != null) {
                sb.operator(" := ")
                vd.init!!.accept(this)
            }

            sb.keyword("END_VAR").close()
        }
        sb.close()

    }


    override fun visit(commentStatement: CommentStatement) {
        if (isPrintComments) {
            sb.cliFormat(COMMENT).printf("{*").printf(commentStatement.comment).printf("*}")
            sb.close()
        }


    }

    /**
     *
     * clear.
     */
    fun clear() {
        sb = HTMLCodeWriter()
    }

    fun closeHtml() {
        sb.printf("</body></html>")
    }
}
*/