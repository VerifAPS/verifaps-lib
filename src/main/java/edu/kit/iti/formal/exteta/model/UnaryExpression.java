package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class UnaryExpression extends Expression {
	public Operator op;
	public Expression expr;

	public UnaryExpression(Operator op, Expression ast) {
		this.op = op;
		this.expr = ast;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
