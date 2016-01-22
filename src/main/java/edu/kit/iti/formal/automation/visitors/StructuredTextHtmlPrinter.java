package edu.kit.iti.formal.automation.visitors;

import edu.kit.iti.formal.automation.ast.*;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.util.HTMLCodeWriter;
import edu.kit.iti.formal.automation.datatypes.Any;

/**
 * Created by weigla on 15.06.2014.
 */
public class StructuredTextHtmlPrinter extends DefaultVisitor<Object> {

	private HTMLCodeWriter sb = new HTMLCodeWriter();
	private boolean printComments;

	public boolean isPrintComments() {
		return printComments;
	}

	public void setPrintComments(boolean printComments) {
		this.printComments = printComments;
	}

	@Override
	public Object defaultVisit(Visitable visitable) {
		sb.div(Sections.ERROR).append("not implemented: ").append(visitable.getClass());
		sb.end();
		return null;
	}

	public String getString() {
		return sb.toString();
	}

	@Override
	public Object visit(ExitStatement exitStatement) {

		sb.div(Sections.STATEMENT, Sections.KEYWORD).append("EXIT");
		sb.end().append(";");
		sb.end();
		return null;
	}

	@Override
	public Object visit(CaseConditions.IntegerCondition integerCondition) {
		sb.div(Sections.CASE_INTEGER_CONDITION);
		integerCondition.getValue().visit(this);
		sb.end();
		return null;
	}

	@Override
	public Object visit(CaseConditions.Enumeration enumeration) {
		sb.div(Sections.CASE_ENUM_CONDITION);
		if (enumeration.getStart() == enumeration.getStop()) {
			sb.appendIdent();
			enumeration.getStart().visit(this);
		} else {
			sb.appendIdent();
			enumeration.getStart().visit(this);
			sb.append("..");
			enumeration.getStop().visit(this);
		}
		sb.end();
		return null;
	}

	@Override
	public Object visit(BinaryExpression binaryExpression) {
		sb.div(Sections.BINARY_EXPRESSION);
		sb.append('(');
		binaryExpression.getLeftExpr().visit(this);
		sb.div(Sections.OPERATOR, Sections.KEYWORD);
		sb.append(" ").append(binaryExpression.getOperator().symbol).append(" ");
		sb.end().end();
		binaryExpression.getRightExpr().visit(this);
		sb.append(')');
		sb.end();
		return null;
	}

	@Override
	public Object visit(AssignmentStatement assignStatement) {
		sb.div(Sections.ASSIGNMENT);
		assignStatement.getVariable().visit(this);
		sb.operator(":=");
		assignStatement.getExpression().visit(this);
		sb.seperator(";").end();
		return null;
	}

	@Override
	public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
		sb.div(Sections.TYPE_DECL_ENUM).div(Sections.TYPE_NAME).append(enumerationTypeDeclaration.getTypeName());
		sb.end().seperator(":");

		sb.div(Sections.TYPE_DECL_DECL).append("(");

		for (String s : enumerationTypeDeclaration.getAllowedValues()) {
			sb.div(Sections.VALUE).append(s);
			sb.end().seperator(",");
		}

		sb.deleteLastSeparator().append(")");
		sb.ts().end().end();
		return null;
	}

	@Override
	public Object visit(RepeatStatement repeatStatement) {
		sb.div(Sections.REPEAT).keyword("REPEAT");
		repeatStatement.getStatements().visit(this);
		sb.keyword(" UNTIL ");
		repeatStatement.getCondition().visit(this);
		sb.keyword("END_REPEAT");
		sb.end();
		return null;
	}

	@Override
	public Object visit(WhileStatement whileStatement) {
		sb.div(Sections.WHILE).keyword("WHILE");
		whileStatement.getCondition().visit(this);
		sb.keyword(" DO ");
		whileStatement.getStatements().visit(this);
		sb.keyword("END_WHILE");
		sb.end();
		return null;
	}

	@Override
	public Object visit(UnaryExpression unaryExpression) {
		sb.div(Sections.UNARY_EXPRESSION, Sections.OPERATOR).append(unaryExpression.getOperator().symbol);
		sb.end().append(" ");
		unaryExpression.getExpression().visit(this);
		sb.end();
		return null;
	}

	@Override
	public Object visit(TypeDeclarations typeDeclarations) {
		sb.div(Sections.TYPE_DECL).keyword("TYPE");
		for (TypeDeclaration decl : typeDeclarations) {
			decl.visit(this);
		}
		sb.keyword("END_TYPE");
		sb.end();
		return null;
	}

	@Override
	public Object visit(CaseStatement caseStatement) {
		sb.div(Sections.CASE_STATEMENT).keyword("CASE");
		caseStatement.getExpression().visit(this);
		sb.keyword(" OF ");
		for (CaseStatement.Case c : caseStatement.getCases()) {
			c.visit(this);
		}
		sb.keyword("END_CASE");
		sb.end();
		return null;
	}

	@Override
	public Object visit(SymbolicReference symbolicReference) {
		sb.variable(symbolicReference.getIdentifier());

		if (symbolicReference.getSubscripts() != null && !symbolicReference.getSubscripts().isEmpty()) {

			sb.div(Sections.SUBSCRIPT).append('[');
			for (Expression expr : symbolicReference.getSubscripts()) {
				expr.visit(this);
				sb.append(',');
			}
			sb.append(']');
			sb.end();
		}

		if (symbolicReference.getSub() != null) {
			sb.append(".");
			symbolicReference.getSub().visit(this);
		}
		return null;
	}

	@Override
	public Object visit(StatementList statements) {
		sb.div(Sections.STATEMENT_BLOCK);
		for (Statement stmt : statements) {
			if (stmt == null) {
				sb.append("{*ERROR: stmt null*}");
			} else {
				sb.div(Sections.STATEMENT);
				stmt.visit(this);
				sb.end();
			}
		}
		sb.end();
		return null;
	}

	@Override
	public Object visit(ProgramDeclaration programDeclaration) {
		sb.div(Sections.PROGRAM).keyword("PROGRAM");
		sb.div(Sections.VARIABLE).append(programDeclaration.getProgramName());
		sb.end().append('\n');

		programDeclaration.getScope().visit(this);

		programDeclaration.getProgramBody().visit(this);
		sb.keyword("END_PROGRAM");
		sb.end();
		return null;
	}

	@Override
	public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
		sb.div(Sections.VALUE).span(tsScalarValue.getDataType().getName())
				.append(tsScalarValue.getDataType().repr(tsScalarValue.getValue()));
		sb.end().end();
		return null;
	}

	@Override
	public Object visit(ExpressionList expressions) {
		sb.append(Sections.EXPRESSION_LIST);
		for (Expression e : expressions) {
			e.visit(this);
			sb.seperator(",");
		}
		sb.deleteLastSeparator().end();
		return null;
	}

	@Override
	public Object visit(FunctionCall functionCall) {
		sb.div(Sections.FUNC_CALL);
		sb.append(functionCall.getFunctionName()).append("(");

		boolean params = false;
		for (FunctionCall.Parameter entry : functionCall.getParameters()) {
			if (entry.getName() != null) {
				sb.variable(entry.getName()).append(entry.isOutput() ? " => " : " := ");
			}
			entry.getExpression().visit(this);
			sb.seperator(",");
			params = true;
		}

		if (params)
			sb.deleteLastSeparator();
		sb.append(");");
		return null;
	}

	@Override
	public Object visit(ForStatement forStatement) {
		sb.div(Sections.FOR);
		sb.keyword("FOR");
		sb.variable(forStatement.getVariable());
		sb.append(" := ");
		forStatement.getStart().visit(this);
		sb.keyword("TO");
		forStatement.getStop().visit(this);
		sb.keyword("DO");
		forStatement.getStatements().visit(this);
		sb.decreaseIndent().nl();
		sb.append("END_FOR");
		sb.end();
		return null;
	}

	@Override
	public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
		sb.div(Sections.FB).keyword("FUNCTION_BLOCK ").variable(functionBlockDeclaration.getFunctionBlockName());

		functionBlockDeclaration.getScope().visit(this);

		functionBlockDeclaration.getFunctionBody().visit(this);
		sb.keyword("END_FUNCTION_BLOCK").ts().end();
		return null;
	}

	@Override
	public Object visit(ReturnStatement returnStatement) {
		sb.keyword("RETURN").ts();
		return null;
	}

	@Override
	public Object visit(IfStatement ifStatement) {
		sb.div(Sections.IFSTATEMENT);

		for (int i = 0; i < ifStatement.getConditionalBranches().size(); i++) {
			if (i == 0)
				sb.keyword("IF");
			else
				sb.keyword("ELSIF");

			ifStatement.getConditionalBranches().get(i).getCondition().visit(this);
			sb.keyword("THEN");
			sb.div("thenblock");
			ifStatement.getConditionalBranches().get(i).getStatements().visit(this);
			sb.end();
		}

		if (ifStatement.getElseBranch().size() > 0) {
			sb.keyword("ELSE");
			ifStatement.getElseBranch().visit(this);
		}
		sb.keyword("END_IF").ts().end();
		return null;
	}

	@Override
	public Object visit(FunctionCallStatement functionCallStatement) {
		sb.div(Sections.FB_CALL);
		functionCallStatement.getFunctionCall().visit(this);
		sb.end();
		return null;
	}

	@Override
	public Object visit(CaseStatement.Case aCase) {
		sb.div(Sections.CASE);
		for (CaseConditions cc : aCase.getConditions()) {
			cc.visit(this);
			sb.seperator(",");
		}
		sb.deleteLastSeparator();
		sb.seperator(":");

		aCase.getStatements().visit(this);
		sb.end();
		return null;
	}

	@Override
	public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
		sb.div(Sections.TYPE_DECL_SIMPLE).type(simpleTypeDeclaration.getBaseTypeName());
		if (simpleTypeDeclaration.getInitializationValue() != null) {
			sb.operator(" := ");
			simpleTypeDeclaration.getInitializationValue().visit(this);
		}
		sb.end();
		return null;
	}

	@Override
	public Object visit(VariableScope variableScope) {
		sb.div(Sections.VARIABLES_DEFINITIONS);
		for (VariableDeclaration vd : variableScope.getVariableMap().values()) {
			vd.getDataType();
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
				vd.getInit().visit(this);
			}

			sb.keyword("END_VAR").end();
		}
		sb.end();
		return null;
	}

	@Override
	public Object visit(CommentStatement commentStatement) {
		if (printComments) {
			sb.div(Sections.COMMENT).append("{*").append(commentStatement.getComment()).append("*}");
			sb.end();
		}
		return null;

	}

	public void clear() {
		sb = new HTMLCodeWriter();
	}

	public void preamble() {
		sb.appendHtmlPreamble();
	}

	public void closeHtml() {
		sb.append("</body></html>");
	}

	public void setCodeWriter(HTMLCodeWriter hcw) {
		sb = hcw;
	}
}
