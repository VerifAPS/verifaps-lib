package stverificationstudio.typechecker;

import stverificationstudio.expressions.Expression;

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
