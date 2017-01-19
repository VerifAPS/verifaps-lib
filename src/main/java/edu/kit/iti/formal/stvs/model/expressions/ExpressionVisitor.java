package edu.kit.iti.formal.stvs.model.expressions;

public interface ExpressionVisitor<R> {

  public R visitFunctionExpr(FunctionExpr functionExpr);

  public R visitLiteral(LiteralExpr literalExpr);

  public R visitVariable(VariableExpr variableExpr);

}
