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

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.util.HTMLCodeWriter
import edu.kit.iti.formal.util.Sections
import edu.kit.iti.formal.util.joinInto

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
open class StructuredTextHtmlPrinter : DefaultVisitor<Unit>() {

    private var sb = HTMLCodeWriter()
    var isPrintComments: Boolean = false
    val string: String
        get() = sb.toString()

    /**
     * {@inheritDoc}
     */
    override fun defaultVisit(obj: Any) {
        sb.div(Sections.ERROR).printf("not implemented: ").print(obj::class.java)
        sb.end()
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(exitStatement: ExitStatement) {

        sb.div(Sections.STATEMENT, Sections.KEYWORD).printf("EXIT")
        sb.end().printf(";")
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(integerCondition: CaseCondition.IntegerCondition) {
        sb.div(Sections.CASE_INTEGER_CONDITION)
        integerCondition.value!!.accept(this)
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumeration: CaseCondition.Enumeration) {
        sb.div(Sections.CASE_ENUM_CONDITION)
        if (enumeration.start === enumeration.stop) {
            sb.appendIdent()
            enumeration.start.accept(this)
        } else {
            sb.appendIdent()
            enumeration.start.accept(this)
            sb.printf("..")
            enumeration.stop!!.accept(this)
        }
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression) {
        sb.div(Sections.BINARY_EXPRESSION)
        sb.append('(')
        binaryExpression.leftExpr!!.accept(this)
        sb.div(Sections.OPERATOR, Sections.KEYWORD)
        sb.printf(" ").printf(binaryExpression.operator!!.symbol).printf(" ")
        sb.end().end()
        binaryExpression.rightExpr!!.accept(this)
        sb.append(')')
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(assignStatement: AssignmentStatement) {
        sb.div(Sections.ASSIGNMENT)
        assignStatement.location.accept(this)
        sb.operator(":=")
        assignStatement.expression.accept(this)
        sb.seperator(";").end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        sb.div(Sections.TYPE_DECL_ENUM).div(Sections.TYPE_NAME).printf(enumerationTypeDeclaration.name)
        sb.end().seperator(":")

        sb.div(Sections.TYPE_DECL_DECL).printf("(")

        for (s in enumerationTypeDeclaration.allowedValues) {
            sb.div(Sections.VALUE).printf(s.text)
            sb.end().seperator(",")
        }

        sb.printf(")")
        sb.ts().end().end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement) {
        sb.div(Sections.REPEAT).keyword("REPEAT")
        repeatStatement.statements.accept(this)
        sb.keyword(" UNTIL ")
        repeatStatement.condition.accept(this)
        sb.keyword("END_REPEAT")
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement) {
        sb.div(Sections.WHILE).keyword("WHILE")
        whileStatement.condition.accept(this)
        sb.keyword(" DO ")
        whileStatement.statements.accept(this)
        sb.keyword("END_WHILE")
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression) {
        sb.div(Sections.UNARY_EXPRESSION, Sections.OPERATOR)
                .printf(unaryExpression.operator.symbol)
        sb.end().printf(" ")
        unaryExpression.expression.accept(this)
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations) {
        sb.div(Sections.TYPE_DECL).keyword("TYPE")
        for (decl in typeDeclarations) {
            decl.accept(this)
        }
        sb.keyword("END_TYPE")
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(caseStatement: CaseStatement) {
        sb.div(Sections.CASE_STATEMENT).keyword("CASE")
        caseStatement.expression!!.accept(this)
        sb.keyword(" OF ")
        for (c in caseStatement.cases) {
            c.accept(this)
        }
        sb.keyword("END_CASE")
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(symbolicReference: Location) {
        /*TODO
        sb.variable(symbolicReference.getName());


		if (symbolicReference.getSubscripts() != null && !symbolicReference.getSubscripts().isEmpty()) {

			sb.div(Sections.SUBSCRIPT).printf('[');
			for (Expression expr : symbolicReference.getSubscripts()) {
				expr.accept(this);
				sb.printf(',');
			}
			sb.printf(']');
			sb.end();
		}

		if (symbolicReference.getSub() != null) {
			sb.printf(".");
			symbolicReference.getSub().accept(this);
		}*/

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(statements: StatementList) {
        sb.div(Sections.STATEMENT_BLOCK)
        for (stmt in statements) {
            if (stmt == null) {
                sb.printf("{*ERROR: stmt null*}")
            } else {
                sb.div(Sections.STATEMENT)
                stmt.accept(this)
                sb.end()
            }
        }
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(programDeclaration: ProgramDeclaration) {
        sb.div(Sections.PROGRAM).keyword("PROGRAM")
        sb.div(Sections.VARIABLE).printf(programDeclaration.name)
        sb.end().append('\n')

        programDeclaration.scope.accept(this)

        programDeclaration.stBody!!.accept(this)
        sb.keyword("END_PROGRAM")
        sb.end()

    }

    /**
     * {@inheritDoc}
     *
     * @Override public Object visit(ScalarValue tsScalarValue) {
     * sb.div(Sections.VALUE).span(tsScalarValue.getDataType().getName())
     * .printf(tsScalarValue.getDataType().repr(tsScalarValue.getValue()));
     * sb.end().end();
     * ;
     * }
     */

    /**
     * {@inheritDoc}
     */
    override fun visit(expressions: ExpressionList) {
        sb.print(Sections.EXPRESSION_LIST)
        for (e in expressions) {
            e.accept(this)
            sb.seperator(",")
        }//TODO
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(invocation: Invocation) {
        sb.div(Sections.FUNC_CALL)
        sb.printf(invocation.calleeName)
        visitInvocationParameters(invocation.parameters)

    }

    private fun visitInvocationParameters(parameters: MutableList<InvocationParameter>) {
        sb.printf("(")
        parameters.joinInto(sb, ",") { it.accept(this) }
        sb.printf(")")
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement) {
        sb.div(Sections.FOR)
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
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        sb.div(Sections.FB).keyword("FUNCTION_BLOCK ").variable(functionBlockDeclaration.name)

        functionBlockDeclaration.scope.accept(this)

        functionBlockDeclaration.stBody!!.accept(this)
        sb.keyword("END_FUNCTION_BLOCK").ts().end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(returnStatement: ReturnStatement) {
        sb.keyword("RETURN").ts()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(ifStatement: IfStatement) {
        sb.div(Sections.IFSTATEMENT)

        for (i in 0 until ifStatement.conditionalBranches.size) {
            if (i == 0)
                sb.keyword("IF")
            else
                sb.keyword("ELSIF")

            ifStatement.conditionalBranches[i].condition.accept(this)
            sb.keyword("THEN")
            sb.div("thenblock")
            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.end()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.keyword("ELSE")
            ifStatement.elseBranch.accept(this)
        }
        sb.keyword("END_IF").ts().end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(fbc: InvocationStatement) {
        fbc.callee.accept(this)
        visitInvocationParameters(fbc.parameters)
        sb.printf(";")
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: Case) {
        sb.div(Sections.CASE)
        for (cc in aCase.conditions) {
            cc.accept(this)
            sb.seperator(",")
        }
        //TODO
        sb.seperator(":")

        aCase.statements.accept(this)
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        sb.div(Sections.TYPE_DECL_SIMPLE).type(simpleTypeDeclaration.baseType.identifier)
        if (simpleTypeDeclaration.initialization != null) {
            sb.operator(" := ")
            simpleTypeDeclaration.initialization!!.accept(this)
        }
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(localScope: Scope) {
        sb.div(Sections.VARIABLES_DEFINITIONS)
        for (vd in localScope.variables) {
            sb.div(Sections.VARIABLES_DEFINITION)

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

            sb.keyword("END_VAR").end()
        }
        sb.end()

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(commentStatement: CommentStatement) {
        if (isPrintComments) {
            sb.div(Sections.COMMENT).printf("{*").printf(commentStatement.comment).printf("*}")
            sb.end()
        }


    }

    /**
     *
     * clear.
     */
    fun clear() {
        sb = HTMLCodeWriter()
    }

    /**
     *
     * preamble.
     */
    fun preamble() {
        sb.appendHtmlPreamble()
    }

    /**
     *
     * closeHtml.
     */
    fun closeHtml() {
        sb.printf("</body></html>")
    }

    /**
     *
     * setCodeWriter.
     *
     * @param hcw a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun setCodeWriter(hcw: HTMLCodeWriter) {
        sb = hcw
    }
}
