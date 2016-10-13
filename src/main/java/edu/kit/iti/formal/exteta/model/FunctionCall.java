package edu.kit.iti.formal.exteta.model;

import java.util.List;

import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class FunctionCall extends Expression {

	public List<Expression> arguments;
	public String fnname;

	public FunctionCall(String text, List<Expression> args) {
		arguments = args;
		fnname = text;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
