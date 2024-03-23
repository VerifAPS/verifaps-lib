package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Created by philipp on 17.01.17.
 */
public final class SimpleExpressions {

  private SimpleExpressions() {
  }

  public static Expression negate(Expression e) {
    return new UnaryFunctionExpr(UnaryFunctionExpr.Op.UNARY_MINUS, e);
  }

  public static Expression not(Expression e) {
    return new UnaryFunctionExpr(UnaryFunctionExpr.Op.NOT, e);
  }

  public static Expression and(Expression e1, Expression e2) {
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, e1, e2);
  }

  public static Expression plus(Expression e1, Expression e2) {
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, e1, e2);
  }

  public static Expression minus(Expression e1, Expression e2) {
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, e1, e2);
  }

  public static Expression equal(Expression e1, Expression e2) {
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, e1, e2);
  }

  public static Expression lessThan(Expression e1, Expression e2) {
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.LESS_THAN, e1, e2);
  }

  public static Expression lessEqual(Expression e1, Expression e2) {
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.LESS_EQUALS, e1, e2);
  }

  public static Expression greaterEqual(Expression e1, Expression e2) {
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.GREATER_EQUALS, e1, e2);
  }


  public static Expression var(String name) {
    return new VariableExpr(name);
  }

  public static Expression var(String name, int index) {
    return new VariableExpr(name, index);
  }

  public static Expression literal(int integer) {
    return new LiteralExpr(new ValueInt(integer));
  }

  public static Expression literal(boolean bool) {
    return new LiteralExpr(ValueBool.of(bool));
  }

  public static Expression literal(ValueEnum e) {
    return new LiteralExpr(e);
  }

  public static Expression literalEnum(String value, TypeEnum sourceType) {
    return literal(new ValueEnum(value, sourceType));
  }

}
