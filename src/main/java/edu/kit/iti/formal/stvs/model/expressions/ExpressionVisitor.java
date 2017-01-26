package edu.kit.iti.formal.stvs.model.expressions;

public interface ExpressionVisitor<R> {

  R visitBinaryFunction(BinaryFunctionExpr binaryFunctionExpr);
  R visitUnaryFunction(UnaryFunctionExpr unaryFunctionExpr);
  R visitLiteral(LiteralExpr literalExpr);
  R visitVariable(VariableExpr variableExpr);

}
