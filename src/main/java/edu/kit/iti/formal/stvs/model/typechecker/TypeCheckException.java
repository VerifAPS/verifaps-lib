package edu.kit.iti.formal.stvs.model.typechecker;

import edu.kit.iti.formal.stvs.model.expressions.Expression;

public class TypeCheckException extends Exception {
	private static final long serialVersionUID = 1L;
	
	private final Expression mistypedExpression;
	
	public TypeCheckException(Expression mistypedExpression, String message) {
		super(message + "\nIn Expression: " + mistypedExpression);
		this.mistypedExpression = mistypedExpression;
	}

	public Expression getMistypedExpression() {
		return mistypedExpression;
	}

}
