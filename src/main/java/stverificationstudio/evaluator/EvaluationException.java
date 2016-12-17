package stverificationstudio.evaluator;

import stverificationstudio.expressions.Expression;

public class EvaluationException extends RuntimeException {

	private static final long serialVersionUID = 1L;
	
	private final Expression expr;
	
	public EvaluationException(Expression expr, String message) {
		super(message);
		this.expr = expr;
	}

	public Expression getExpr() {
		return expr;
	}

}
