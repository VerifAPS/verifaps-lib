package edu.kit.iti.formal.stvs.model.expressions;

/**
 * The visitor for the compositum of {@link Expression}s.
 * @param <R> the return type of this visit. It has to be defined
 *           at the class-level, because all implemented methods must
 *           return the same type.
 */
public interface ExpressionVisitor<R> {

  R visitBinaryFunction(BinaryFunctionExpr binaryFunctionExpr);

  R visitUnaryFunction(UnaryFunctionExpr unaryFunctionExpr);

  R visitLiteral(LiteralExpr literalExpr);

  R visitVariable(VariableExpr variableExpr);

}
