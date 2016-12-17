package stverificationstudio.evaluator;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import stverificationstudio.expressions.Expression;
import stverificationstudio.expressions.ExpressionVisitor;
import stverificationstudio.expressions.FunctionExpr;
import stverificationstudio.expressions.LiteralExpr;
import stverificationstudio.expressions.Value;
import stverificationstudio.expressions.ValueInt;
import stverificationstudio.expressions.VariableExpr;

public class Evaluator implements ExpressionVisitor<Value> {
	
	private Map<String,Value> context;
	
	public Evaluator(Map<String,Value> initialContext) {
		this.setContext(initialContext);
	}
	
	public Value evaluate(Expression expr) throws EvaluationException{
		return expr.takeVisitor(this);
	}

	@Override
	public Value visitFunctionExpr(FunctionExpr functionExpr) {
		switch(functionExpr.getOperation()) {
		case PLUS: return evaluatePlus(functionExpr);
		default:
			throw new EvaluationException(
					functionExpr,
					"Unkown operator: " + functionExpr.getOperation());
		}
	}

	@Override
	public Value visitLiteral(LiteralExpr literalExpr) {
		return literalExpr.getValue();
	}

	@Override
	public Value visitVariable(VariableExpr variableExpr) {
		return context.get(variableExpr.getVariableName());
	}

	public Map<String,Value> getContext() {
		return context;
	}

	public void setContext(Map<String,Value> context) {
		this.context = context;
	}

	private <R> R throwTypeException(Expression expr, String expectedType, String actualType) {
		throw new EvaluationException(
				expr, 
				"Expected type: " + expectedType + ", but instead got: " + actualType);
	}
	
	private Value evaluatePlus(FunctionExpr functionExpr) {
		// This is where the recursion happens!
		// calling evaluate makes the subexpressions be visited in turn
		List<Value> values = functionExpr.getArguments()
			.stream().map(this::evaluate).collect(Collectors.toList());
		
		if (values.size() != 2) {
			throw new EvaluationException(
					functionExpr, 
					"Number of arguments should be 2, but is " + values.size() + ".");
		}
		
		Value leftSummandValue = values.get(0);
		Value rightSummandValue = values.get(1);
		
		int leftSummand = leftSummandValue.match(
				(value) -> value, 
				(bool) -> throwTypeException(functionExpr, "Int", "Bool"), 
				(enumName) -> throwTypeException(functionExpr, "Int", "Enum"));

		int rightSummand = rightSummandValue.match(
				(value) -> value, 
				(bool) -> throwTypeException(functionExpr, "Int", "Bool"), 
				(enumName) -> throwTypeException(functionExpr, "Int", "Enum"));
		
		return new ValueInt(leftSummand + rightSummand);
	}

}
