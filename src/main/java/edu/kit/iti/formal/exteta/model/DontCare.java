package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class DontCare extends Expression {
	public static final DontCare DONTCARE = new DontCare();

	private DontCare() {
	}
	
	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}