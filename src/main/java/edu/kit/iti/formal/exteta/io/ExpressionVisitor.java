package edu.kit.iti.formal.exteta.io;

import edu.kit.iti.formal.exteta.model.*;

public interface ExpressionVisitor<T> {

	T visit(UnaryExpression unaryExpression);

	T visit(IntervalExpression intervalExpression);

	T visit(FunctionCall functionCall);

	T visit(DontCare dontCare);

	T visit(ConstantExpression constantExpression);

	T visit(IfExpr ifExpr);

	T visit(Name name);

	T visit(BinaryExpression binaryExpression);
}
