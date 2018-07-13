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
import edu.kit.iti.formal.automation.st.util.HTMLCodeWriter
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Sections
import edu.kit.iti.formal.automation.visitors.Visitable
import org.antlr.v4.runtime.Token

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
        sb.div(Sections.ERROR).append("not implemented: ").append(obj::class.java)
        sb.end()
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(exitStatement: ExitStatement): Unit? {

        sb.div(Sections.STATEMENT, Sections.KEYWORD).append("EXIT")
        sb.end().append(";")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(integerCondition: CaseCondition.IntegerCondition): Unit? {
        sb.div(Sections.CASE_INTEGER_CONDITION)
        integerCondition.value!!.accept(this)
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumeration: CaseCondition.Enumeration): Unit? {
        sb.div(Sections.CASE_ENUM_CONDITION)
        if (enumeration.start === enumeration.stop) {
            sb.appendIdent()
            enumeration.start.accept(this)
        } else {
            sb.appendIdent()
            enumeration.start.accept(this)
            sb.append("..")
            enumeration.stop!!.accept(this)
        }
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression): Unit? {
        sb.div(Sections.BINARY_EXPRESSION)
        sb.append('(')
        binaryExpression.leftExpr!!.accept(this)
        sb.div(Sections.OPERATOR, Sections.KEYWORD)
        sb.append(" ").append(binaryExpression.operator!!.symbol).append(" ")
        sb.end().end()
        binaryExpression.rightExpr!!.accept(this)
        sb.append(')')
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(assignStatement: AssignmentStatement): Unit? {
        sb.div(Sections.ASSIGNMENT)
        assignStatement.location.accept(this)
        sb.operator(":=")
        assignStatement.expression.accept(this)
        sb.seperator(";").end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): Unit? {
        sb.div(Sections.TYPE_DECL_ENUM).div(Sections.TYPE_NAME).append(enumerationTypeDeclaration.name)
        sb.end().seperator(":")

        sb.div(Sections.TYPE_DECL_DECL).append("(")

        for (s in enumerationTypeDeclaration.allowedValues) {
            sb.div(Sections.VALUE).append(s.text)
            sb.end().seperator(",")
        }

        sb.append(")")
        sb.ts().end().end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement): Unit? {
        sb.div(Sections.REPEAT).keyword("REPEAT")
        repeatStatement.statements.accept(this)
        sb.keyword(" UNTIL ")
        repeatStatement.condition.accept(this)
        sb.keyword("END_REPEAT")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement): Unit? {
        sb.div(Sections.WHILE).keyword("WHILE")
        whileStatement.condition.accept(this)
        sb.keyword(" DO ")
        whileStatement.statements.accept(this)
        sb.keyword("END_WHILE")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression): Unit? {
        sb.div(Sections.UNARY_EXPRESSION, Sections.OPERATOR)
                .append(unaryExpression.operator.symbol)
        sb.end().append(" ")
        unaryExpression.expression.accept(this)
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations): Unit? {
        sb.div(Sections.TYPE_DECL).keyword("TYPE")
        for (decl in typeDeclarations) {
            decl.accept(this)
        }
        sb.keyword("END_TYPE")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(caseStatement: CaseStatement): Unit? {
        sb.div(Sections.CASE_STATEMENT).keyword("CASE")
        caseStatement.expression!!.accept(this)
        sb.keyword(" OF ")
        for (c in caseStatement.cases) {
            c.accept(this)
        }
        sb.keyword("END_CASE")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(symbolicReference: Location): Unit? {
        /*TODO
        sb.variable(symbolicReference.getName());


		if (symbolicReference.getSubscripts() != null && !symbolicReference.getSubscripts().isEmpty()) {

			sb.div(Sections.SUBSCRIPT).append('[');
			for (Expression expr : symbolicReference.getSubscripts()) {
				expr.accept(this);
				sb.append(',');
			}
			sb.append(']');
			sb.end();
		}

		if (symbolicReference.getSub() != null) {
			sb.append(".");
			symbolicReference.getSub().accept(this);
		}*/
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(statements: StatementList): Unit? {
        sb.div(Sections.STATEMENT_BLOCK)
        for (stmt in statements) {
            if (stmt == null) {
                sb.append("{*ERROR: stmt null*}")
            } else {
                sb.div(Sections.STATEMENT)
                stmt.accept(this)
                sb.end()
            }
        }
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(programDeclaration: ProgramDeclaration): Unit? {
        sb.div(Sections.PROGRAM).keyword("PROGRAM")
        sb.div(Sections.VARIABLE).append(programDeclaration.name)
        sb.end().append('\n')

        programDeclaration.scope.accept(this)

        programDeclaration.stBody!!.accept(this)
        sb.keyword("END_PROGRAM")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     *
     * @Override public Object visit(ScalarValue tsScalarValue) {
     * sb.div(Sections.VALUE).span(tsScalarValue.getDataType().getName())
     * .append(tsScalarValue.getDataType().repr(tsScalarValue.getValue()));
     * sb.end().end();
     * return null;
     * }
     */

    /**
     * {@inheritDoc}
     */
    override fun visit(expressions: ExpressionList): Unit? {
        sb.append(Sections.EXPRESSION_LIST)
        for (e in expressions) {
            e.accept(this)
            sb.seperator(",")
        }//TODO
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(invocation: Invocation): Unit? {
        sb.div(Sections.FUNC_CALL)
        sb.append(invocation.calleeName).append("(")

        var params = false
        for (entry in invocation.parameters) {
            entry.accept(this)
            sb.seperator(",")
            params = true
        }

        //TODO
        sb.append(");")
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement): Unit? {
        sb.div(Sections.FOR)
        sb.keyword("FOR")
        sb.variable(forStatement.variable!!)
        sb.append(" := ")
        forStatement.start!!.accept(this)
        sb.keyword("TO")
        forStatement.stop!!.accept(this)
        sb.keyword("DO")
        forStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.append("END_FOR")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Unit? {
        sb.div(Sections.FB).keyword("FUNCTION_BLOCK ").variable(functionBlockDeclaration.name)

        functionBlockDeclaration.scope.accept(this)

        functionBlockDeclaration.stBody!!.accept(this)
        sb.keyword("END_FUNCTION_BLOCK").ts().end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(returnStatement: ReturnStatement): Unit? {
        sb.keyword("RETURN").ts()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(ifStatement: IfStatement): Unit? {
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
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(fbc: InvocationStatement): Unit? {
        fbc.invocation.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: Case): Unit? {
        sb.div(Sections.CASE)
        for (cc in aCase.conditions) {
            cc.accept(this)
            sb.seperator(",")
        }
        //TODO
        sb.seperator(":")

        aCase.statements.accept(this)
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): Unit? {
        sb.div(Sections.TYPE_DECL_SIMPLE).type(simpleTypeDeclaration.baseType.identifier)
        if (simpleTypeDeclaration.initialization != null) {
            sb.operator(" := ")
            simpleTypeDeclaration.initialization!!.accept(this)
        }
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(localScope: Scope): Unit? {
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

            sb.append(" ")

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
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(commentStatement: CommentStatement): Unit? {
        if (isPrintComments) {
            sb.div(Sections.COMMENT).append("{*").append(commentStatement.comment).append("*}")
            sb.end()
        }
        return null

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
        sb.append("</body></html>")
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
