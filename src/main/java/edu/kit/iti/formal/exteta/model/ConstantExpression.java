package edu.kit.iti.formal.exteta.model;

import org.antlr.v4.runtime.Token;

import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class ConstantExpression extends Expression {

	public String literal;

	public ConstantExpression(Token start) {
		this(start.getText());
	}

	public ConstantExpression(String text) {
		literal = text;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}

}
