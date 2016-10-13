package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class Name extends Expression {

	public String name;

	public Name(String text) {
		name = text;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}

}
