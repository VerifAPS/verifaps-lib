package edu.kit.iti.formal.exteta.model;

import java.util.LinkedList;

import edu.kit.iti.formal.automation.st.util.Tuple;
import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public class IfExpr extends Expression {
	public LinkedList<Tuple<Expression, Expression>> cases = new LinkedList<>();

	public void addCase(Expression condition, Expression then) {
		cases.add(Tuple.make(condition, then));
	}
	
	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}

}
