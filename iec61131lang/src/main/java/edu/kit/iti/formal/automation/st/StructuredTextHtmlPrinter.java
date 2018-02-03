package edu.kit.iti.formal.automation.st;

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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.HTMLCodeWriter;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Sections;
import edu.kit.iti.formal.automation.visitors.Visitable;
import org.antlr.v4.runtime.Token;

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class StructuredTextHtmlPrinter extends DefaultVisitor<Object> {

    private HTMLCodeWriter sb = new HTMLCodeWriter();
    private boolean printComments;

    /**
     * <p>isPrintComments.</p>
     *
     * @return a boolean.
     */
    public boolean isPrintComments() {
        return printComments;
    }

    /**
     * <p>Setter for the field <code>printComments</code>.</p>
     *
     * @param printComments a boolean.
     */
    public void setPrintComments(boolean printComments) {
        this.printComments = printComments;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object defaultVisit(Visitable visitable) {
        sb.div(Sections.ERROR).append("not implemented: ").append(visitable.getClass());
        sb.end();
        return null;
    }

    /**
     * <p>getString.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getString() {
        return sb.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ExitStatement exitStatement) {

        sb.div(Sections.STATEMENT, Sections.KEYWORD).append("EXIT");
        sb.end().append(";");
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.IntegerCondition integerCondition) {
        sb.div(Sections.CASE_INTEGER_CONDITION);
        integerCondition.getValue().accept(this);
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.Enumeration enumeration) {
        sb.div(Sections.CASE_ENUM_CONDITION);
        if (enumeration.getStart() == enumeration.getStop()) {
            sb.appendIdent();
            enumeration.getStart().accept(this);
        } else {
            sb.appendIdent();
            enumeration.getStart().accept(this);
            sb.append("..");
            enumeration.getStop().accept(this);
        }
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(BinaryExpression binaryExpression) {
        sb.div(Sections.BINARY_EXPRESSION);
        sb.append('(');
        binaryExpression.getLeftExpr().accept(this);
        sb.div(Sections.OPERATOR, Sections.KEYWORD);
        sb.append(" ").append(binaryExpression.getOperator().symbol()).append(" ");
        sb.end().end();
        binaryExpression.getRightExpr().accept(this);
        sb.append(')');
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(AssignmentStatement assignStatement) {
        sb.div(Sections.ASSIGNMENT);
        assignStatement.getLocation().accept(this);
        sb.operator(":=");
        assignStatement.getExpression().accept(this);
        sb.seperator(";").end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        sb.div(Sections.TYPE_DECL_ENUM).div(Sections.TYPE_NAME).append(enumerationTypeDeclaration.getTypeName());
        sb.end().seperator(":");

        sb.div(Sections.TYPE_DECL_DECL).append("(");

        for (Token s : enumerationTypeDeclaration.getAllowedValues()) {
            sb.div(Sections.VALUE).append(s.getText());
            sb.end().seperator(",");
        }

        sb.deleteLastSeparator().append(")");
        sb.ts().end().end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(RepeatStatement repeatStatement) {
        sb.div(Sections.REPEAT).keyword("REPEAT");
        repeatStatement.getStatements().accept(this);
        sb.keyword(" UNTIL ");
        repeatStatement.getCondition().accept(this);
        sb.keyword("END_REPEAT");
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(WhileStatement whileStatement) {
        sb.div(Sections.WHILE).keyword("WHILE");
        whileStatement.getCondition().accept(this);
        sb.keyword(" DO ");
        whileStatement.getStatements().accept(this);
        sb.keyword("END_WHILE");
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(UnaryExpression unaryExpression) {
        sb.div(Sections.UNARY_EXPRESSION, Sections.OPERATOR)
                .append(unaryExpression.getOperator().symbol());
        sb.end().append(" ");
        unaryExpression.getExpression().accept(this);
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(TypeDeclarations typeDeclarations) {
        sb.div(Sections.TYPE_DECL).keyword("TYPE");
        for (TypeDeclaration decl : typeDeclarations) {
            decl.accept(this);
        }
        sb.keyword("END_TYPE");
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement caseStatement) {
        sb.div(Sections.CASE_STATEMENT).keyword("CASE");
        caseStatement.getExpression().accept(this);
        sb.keyword(" OF ");
        for (CaseStatement.Case c : caseStatement.getCases()) {
            c.accept(this);
        }
        sb.keyword("END_CASE");
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(Location symbolicReference) {
    /*TODO
        sb.variable(symbolicReference.getIdentifier());


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
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StatementList statements) {
        sb.div(Sections.STATEMENT_BLOCK);
        for (Statement stmt : statements) {
            if (stmt == null) {
                sb.append("{*ERROR: stmt null*}");
            } else {
                sb.div(Sections.STATEMENT);
                stmt.accept(this);
                sb.end();
            }
        }
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        sb.div(Sections.PROGRAM).keyword("PROGRAM");
        sb.div(Sections.VARIABLE).append(programDeclaration.getProgramName());
        sb.end().append('\n');

        programDeclaration.getScope().accept(this);

        programDeclaration.getStBody().accept(this);
        sb.keyword("END_PROGRAM");
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     *
     @Override public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
     sb.div(Sections.VALUE).span(tsScalarValue.getDataType().getName())
     .append(tsScalarValue.getDataType().repr(tsScalarValue.getValue()));
     sb.end().end();
     return null;
     }*/

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ExpressionList expressions) {
        sb.append(Sections.EXPRESSION_LIST);
        for (Expression e : expressions) {
            e.accept(this);
            sb.seperator(",");
        }
        sb.deleteLastSeparator().end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(Invocation invocation) {
        sb.div(Sections.FUNC_CALL);
        sb.append(invocation.getCalleeName()).append("(");

        boolean params = false;
        for (Invocation.Parameter entry : invocation.getParameters()) {
            entry.accept(this);
            sb.seperator(",");
            params = true;
        }

        if (params)
            sb.deleteLastSeparator();
        sb.append(");");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ForStatement forStatement) {
        sb.div(Sections.FOR);
        sb.keyword("FOR");
        sb.variable(forStatement.getVariable());
        sb.append(" := ");
        forStatement.getStart().accept(this);
        sb.keyword("TO");
        forStatement.getStop().accept(this);
        sb.keyword("DO");
        forStatement.getStatements().accept(this);
        sb.decreaseIndent().nl();
        sb.append("END_FOR");
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        sb.div(Sections.FB).keyword("FUNCTION_BLOCK ").variable(functionBlockDeclaration.getName());

        functionBlockDeclaration.getScope().accept(this);

        functionBlockDeclaration.getStBody().accept(this);
        sb.keyword("END_FUNCTION_BLOCK").ts().end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ReturnStatement returnStatement) {
        sb.keyword("RETURN").ts();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(IfStatement ifStatement) {
        sb.div(Sections.IFSTATEMENT);

        for (int i = 0; i < ifStatement.getConditionalBranches().size(); i++) {
            if (i == 0)
                sb.keyword("IF");
            else
                sb.keyword("ELSIF");

            ifStatement.getConditionalBranches().get(i).getCondition().accept(this);
            sb.keyword("THEN");
            sb.div("thenblock");
            ifStatement.getConditionalBranches().get(i).getStatements().accept(this);
            sb.end();
        }

        if (ifStatement.getElseBranch().size() > 0) {
            sb.keyword("ELSE");
            ifStatement.getElseBranch().accept(this);
        }
        sb.keyword("END_IF").ts().end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(InvocationStatement fbc) {
        fbc.getInvocation().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement.Case aCase) {
        sb.div(Sections.CASE);
        for (CaseCondition cc : aCase.getConditions()) {
            cc.accept(this);
            sb.seperator(",");
        }
        sb.deleteLastSeparator();
        sb.seperator(":");

        aCase.getStatements().accept(this);
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        sb.div(Sections.TYPE_DECL_SIMPLE).type(simpleTypeDeclaration.getBaseTypeName());
        if (simpleTypeDeclaration.getInitialization() != null) {
            sb.operator(" := ");
            simpleTypeDeclaration.getInitialization().accept(this);
        }
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(Scope localScope) {
        sb.div(Sections.VARIABLES_DEFINITIONS);
        for (VariableDeclaration vd : localScope.asMap().values()) {
            sb.div(Sections.VARIABLES_DEFINITION);

            if (vd.isInput())
                sb.keyword("VAR_INPUT");
            else if (vd.isOutput())
                sb.keyword("VAR_OUTPUT");
            else if (vd.isInOut())
                sb.keyword("VAR_INOUT");
            else if (vd.isExternal())
                sb.keyword("VAR_EXTERNAL");
            else if (vd.isGlobal())
                sb.keyword("VAR_GLOBAL");
            else
                sb.keyword("VAR");

            if (vd.isConstant())
                sb.keyword("CONSTANT");

            if (vd.isRetain())
                sb.keyword("RETAIN");
            else
                sb.keyword("NON_RETAIN");

            sb.append(" ");

            sb.variable(vd.getName());

            sb.seperator(":");
            sb.type(vd.getDataTypeName());

            if (vd.getInit() != null) {
                sb.operator(" := ");
                vd.getInit().accept(this);
            }

            sb.keyword("END_VAR").end();
        }
        sb.end();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CommentStatement commentStatement) {
        if (printComments) {
            sb.div(Sections.COMMENT).append("{*").append(commentStatement.getComment()).append("*}");
            sb.end();
        }
        return null;

    }

    /**
     * <p>clear.</p>
     */
    public void clear() {
        sb = new HTMLCodeWriter();
    }

    /**
     * <p>preamble.</p>
     */
    public void preamble() {
        sb.appendHtmlPreamble();
    }

    /**
     * <p>closeHtml.</p>
     */
    public void closeHtml() {
        sb.append("</body></html>");
    }

    /**
     * <p>setCodeWriter.</p>
     *
     * @param hcw a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public void setCodeWriter(HTMLCodeWriter hcw) {
        sb = hcw;
    }
}
