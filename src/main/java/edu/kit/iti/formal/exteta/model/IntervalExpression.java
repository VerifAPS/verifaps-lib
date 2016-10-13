package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class IntervalExpression extends Expression {
	public Expression left, right;

	public IntervalExpression() {
	}

	public IntervalExpression(Expression left2, Expression right2) {
		left = left2;
		right = right2;
	}

	
	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
