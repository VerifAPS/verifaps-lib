package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class BinaryExpression extends Expression {
	public Expression left, right;
	public Operator op;

	public BinaryExpression(Expression l, Operator o, Expression r) {
		left = l;
		right = r;
		op = o;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}

}
