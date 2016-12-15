package edu.kit.iti.formal.exteta.io;

import edu.kit.iti.formal.common.expression.BinaryExpression;
import edu.kit.iti.formal.common.expression.ConstantExpression;
import edu.kit.iti.formal.common.expression.Expression;
import edu.kit.iti.formal.common.expression.FunctionCall;
import edu.kit.iti.formal.common.expression.IfExpr;
import edu.kit.iti.formal.common.expression.IntervalExpression;
import edu.kit.iti.formal.common.expression.Name;
import edu.kit.iti.formal.common.expression.UnaryExpression;

public class ExpressionPrinter implements ExpressionVisitor<String> {
	static ExpressionPrinter PRINTER = new ExpressionPrinter();

	public static String print(Expression expression) {
		return expression.accept(PRINTER);
	}

	@Override
	public String visit(UnaryExpression unaryExpression) {
		return unaryExpression.op.abbrev + "" + unaryExpression.expr.accept(this);
	}

	@Override
	public String visit(IntervalExpression expr) {
		return "[" + expr.left.accept(this) + ", " + expr.right.accept(this) + "]";
	}

	@Override
	public String visit(FunctionCall functionCall) {
		String args = functionCall.arguments.stream().map(a -> a.accept(this)).reduce((a, b) -> a + ", " + b)
				.orElse("");

		return functionCall.fnname + "(" + args + ")";
	}

	@Override
	public String visit(DontCare dontCare) {
		return "~";
	}

	@Override
	public String visit(ConstantExpression literal) {
		return literal.literal;
	}

	@Override
	public String visit(IfExpr ifExpr) {
		String a = "if \n";
		a += ifExpr.cases.stream().map(c -> "::" + c.a.accept(this) + "->" + c.a.accept(this))
				.reduce((x, y) -> x + "\n" + y).orElse("");
		a += "\nfi";
		return a;
	}

	@Override
	public String visit(Name name) {
		return name.name;
	}

	@Override
	public String visit(BinaryExpression bexpr) {
		return "(" + bexpr.left.accept(this) + bexpr.op.abbrev + bexpr.right.accept(this) + ")";
	}
}
