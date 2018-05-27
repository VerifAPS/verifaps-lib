package edu.kit.iti.formal.automation.st

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
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
open class StructuredTextHtmlPrinter : DefaultVisitor<Any>() {

    private var sb = HTMLCodeWriter()
    /**
     *
     * isPrintComments.
     *
     * @return a boolean.
     */
    /**
     *
     * Setter for the field `printComments`.
     *
     * @param printComments a boolean.
     */
    var isPrintComments: Boolean = false

    /**
     *
     * getString.
     *
     * @return a [java.lang.String] object.
     */
    val string: String
        get() = sb.toString()

    /**
     * {@inheritDoc}
     */
    override fun defaultVisit(visitable: Visitable): Any? {
        sb.div(Sections.ERROR).append("not implemented: ").append(visitable.javaClass)
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(exitStatement: ExitStatement): Any? {

        sb.div(Sections.STATEMENT, Sections.KEYWORD).append("EXIT")
        sb.end().append(";")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(integerCondition: CaseCondition.IntegerCondition): Any? {
        sb.div(Sections.CASE_INTEGER_CONDITION)
        integerCondition.value!!.accept<Any>(this)
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumeration: CaseCondition.Enumeration): Any? {
        sb.div(Sections.CASE_ENUM_CONDITION)
        if (enumeration.start === enumeration.stop) {
            sb.appendIdent()
            enumeration.start.accept<Any>(this)
        } else {
            sb.appendIdent()
            enumeration.start.accept<Any>(this)
            sb.append("..")
            enumeration.stop!!.accept<Any>(this)
        }
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression): Any? {
        sb.div(Sections.BINARY_EXPRESSION)
        sb.append('(')
        binaryExpression.leftExpr!!.accept<Any>(this)
        sb.div(Sections.OPERATOR, Sections.KEYWORD)
        sb.append(" ").append(binaryExpression.operator!!.symbol()).append(" ")
        sb.end().end()
        binaryExpression.rightExpr!!.accept<Any>(this)
        sb.append(')')
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(assignStatement: AssignmentStatement): Any? {
        sb.div(Sections.ASSIGNMENT)
        assignStatement.location.accept<Any>(this)
        sb.operator(":=")
        assignStatement.expression.accept<Any>(this)
        sb.seperator(";").end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): Any? {
        sb.div(Sections.TYPE_DECL_ENUM).div(Sections.TYPE_NAME).append(enumerationTypeDeclaration.typeName)
        sb.end().seperator(":")

        sb.div(Sections.TYPE_DECL_DECL).append("(")

        for (s in enumerationTypeDeclaration.allowedValues) {
            sb.div(Sections.VALUE).append(s.text)
            sb.end().seperator(",")
        }

        sb.deleteLastSeparator().append(")")
        sb.ts().end().end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement): Any? {
        sb.div(Sections.REPEAT).keyword("REPEAT")
        repeatStatement.statements.accept(this)
        sb.keyword(" UNTIL ")
        repeatStatement.condition.accept<Any>(this)
        sb.keyword("END_REPEAT")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement): Any? {
        sb.div(Sections.WHILE).keyword("WHILE")
        whileStatement.condition.accept<Any>(this)
        sb.keyword(" DO ")
        whileStatement.statements.accept(this)
        sb.keyword("END_WHILE")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression): Any? {
        sb.div(Sections.UNARY_EXPRESSION, Sections.OPERATOR)
                .append(unaryExpression.operator.symbol())
        sb.end().append(" ")
        unaryExpression.expression.accept<Any>(this)
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations): Any? {
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
    override fun visit(caseStatement: CaseStatement): Any? {
        sb.div(Sections.CASE_STATEMENT).keyword("CASE")
        caseStatement.expression!!.accept<Any>(this)
        sb.keyword(" OF ")
        for (c in caseStatement.cases) {
            c.accept<Any>(this)
        }
        sb.keyword("END_CASE")
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(symbolicReference: Location): Any? {
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
    override fun visit(statements: StatementList): Any? {
        sb.div(Sections.STATEMENT_BLOCK)
        for (stmt in statements) {
            if (stmt == null) {
                sb.append("{*ERROR: stmt null*}")
            } else {
                sb.div(Sections.STATEMENT)
                stmt.accept<Any>(this)
                sb.end()
            }
        }
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(programDeclaration: ProgramDeclaration): Any? {
        sb.div(Sections.PROGRAM).keyword("PROGRAM")
        sb.div(Sections.VARIABLE).append(programDeclaration.programName)
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
    override fun visit(expressions: ExpressionList): Any? {
        sb.append(Sections.EXPRESSION_LIST)
        for (e in expressions) {
            e.accept<Any>(this)
            sb.seperator(",")
        }
        sb.deleteLastSeparator().end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(invocation: Invocation): Any? {
        sb.div(Sections.FUNC_CALL)
        sb.append(invocation.calleeName).append("(")

        var params = false
        for (entry in invocation.parameters) {
            entry.accept(this)
            sb.seperator(",")
            params = true
        }

        if (params)
            sb.deleteLastSeparator()
        sb.append(");")
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement): Any? {
        sb.div(Sections.FOR)
        sb.keyword("FOR")
        sb.variable(forStatement.variable)
        sb.append(" := ")
        forStatement.start!!.accept<Any>(this)
        sb.keyword("TO")
        forStatement.stop!!.accept<Any>(this)
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
    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Any? {
        sb.div(Sections.FB).keyword("FUNCTION_BLOCK ").variable(functionBlockDeclaration.name)

        functionBlockDeclaration.scope.accept(this)

        functionBlockDeclaration.stBody!!.accept(this)
        sb.keyword("END_FUNCTION_BLOCK").ts().end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(returnStatement: ReturnStatement): Any? {
        sb.keyword("RETURN").ts()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(ifStatement: IfStatement): Any? {
        sb.div(Sections.IFSTATEMENT)

        for (i in 0 until ifStatement.conditionalBranches.size) {
            if (i == 0)
                sb.keyword("IF")
            else
                sb.keyword("ELSIF")

            ifStatement.conditionalBranches[i].condition.accept<Any>(this)
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
    override fun visit(fbc: InvocationStatement): Any? {
        fbc.invocation.accept<Any>(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: CaseStatement.Case): Any? {
        sb.div(Sections.CASE)
        for (cc in aCase.conditions) {
            cc.accept<Any>(this)
            sb.seperator(",")
        }
        sb.deleteLastSeparator()
        sb.seperator(":")

        aCase.statements.accept(this)
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration<*>): Any? {
        sb.div(Sections.TYPE_DECL_SIMPLE).type(simpleTypeDeclaration.baseTypeName)
        if (simpleTypeDeclaration.initialization != null) {
            sb.operator(" := ")
            simpleTypeDeclaration.initialization!!.accept<Any>(this)
        }
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(localScope: Scope): Any? {
        sb.div(Sections.VARIABLES_DEFINITIONS)
        for (vd in localScope.asMap().values) {
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
            sb.type(vd.dataTypeName)

            if (vd.init != null) {
                sb.operator(" := ")
                vd.init!!.accept<Any>(this)
            }

            sb.keyword("END_VAR").end()
        }
        sb.end()
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(commentStatement: CommentStatement): Any? {
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
