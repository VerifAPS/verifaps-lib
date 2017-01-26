package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Map;

public class TypeChecker implements ExpressionVisitor<Type> {

  private static class InternalTypeCheckException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    private final Expression mistypedExpression;

    public InternalTypeCheckException(Expression mistypedExpression, String message) {
      super(message);
      this.mistypedExpression = mistypedExpression;
    }

    public Expression getMistypedExpression() {
      return mistypedExpression;
    }

  }

  private final Map<String, Type> variableTypeContext;

  public TypeChecker(Map<String, Type> variableTypeContext) {
    this.variableTypeContext = variableTypeContext;
  }

  public Type typeCheck(Expression expr) throws TypeCheckException {
    try {
      return expr.takeVisitor(this);
    } catch (InternalTypeCheckException e) {
      throw new TypeCheckException(
          e.getMistypedExpression(),
          e.getMessage());
    }
  }

  @Override
  public Type visitUnaryFunction(UnaryFunctionExpr unaryFunctionExpr) {
    Type argType = unaryFunctionExpr.getArgument().takeVisitor(this);
    switch (unaryFunctionExpr.getOperation()) {
      case NOT:
        assertTypeEquality(TypeBool.BOOL, argType, unaryFunctionExpr);
        return TypeBool.BOOL;
      case UNARY_MINUS:
        assertTypeEquality(TypeInt.INT, argType, unaryFunctionExpr);
        return TypeInt.INT;
      default:
        return throwUnkownOperation(unaryFunctionExpr.getOperation().toString(), unaryFunctionExpr);
    }
  }

  @Override
  public Type visitBinaryFunction(BinaryFunctionExpr binaryFunctionExpr) {
    Type firstArgType = binaryFunctionExpr.getFirstArgument().takeVisitor(this);
    Type secondArgType = binaryFunctionExpr.getSecondArgument().takeVisitor(this);
    switch (binaryFunctionExpr.getOperation()) {
      // (INT, INT) -> INT
      case PLUS:
      case MINUS:
      case MULTIPLICATION:
      case DIVISION:
      case MODULO:
      case POWER:
        assertTypeEquality(TypeInt.INT, firstArgType, binaryFunctionExpr);
        assertTypeEquality(TypeInt.INT, secondArgType, binaryFunctionExpr);
        return TypeInt.INT;
      // (BOOL, BOOL) -> BOOL
      case AND:
      case OR:
      case XOR:
        assertTypeEquality(TypeBool.BOOL, firstArgType, binaryFunctionExpr);
        assertTypeEquality(TypeBool.BOOL, secondArgType, binaryFunctionExpr);
        return TypeBool.BOOL;
      // (INT, INT) -> BOOL
      case GREATER_THAN:
      case GREATER_EQUALS:
      case LESS_THAN:
      case LESS_EQUALS:
        assertTypeEquality(TypeInt.INT, firstArgType, binaryFunctionExpr);
        assertTypeEquality(TypeInt.INT, secondArgType, binaryFunctionExpr);
        return TypeBool.BOOL;
      // (a, a) -> BOOL
      case EQUALS:
      case NOT_EQUALS:
        assertEqualTypes(firstArgType, secondArgType, binaryFunctionExpr);
        return TypeBool.BOOL;
      default:
        return throwUnkownOperation(binaryFunctionExpr.getOperation().toString(), binaryFunctionExpr);
    }
  }

  private void assertTypeEquality(Type expectedType, Type actualType, Expression expr) {
    if (!actualType.checksAgainst(expectedType)) {
      throw new InternalTypeCheckException(expr,
          "Expected type \"" + expectedType.getTypeName() + "\"," +
              "but got \"" + actualType.getTypeName() + "\"");
    }
  }

  // Almost Only differs in error message from assertTypeEquality
  private void assertEqualTypes(Type type1, Type type2, Expression expr) {
    if (!type1.equals(type2)) {
      throw new InternalTypeCheckException(expr,
          "Expected equal types, but got 2 different types: \"" + type1.getTypeName() + "\"" +
              " and \"" + type2.getTypeName() + "\"");
    }
  }

  private <A> A throwUnkownOperation(String operationName, Expression expr) {
    throw new InternalTypeCheckException(expr, "Unknown Operation \"" + operationName + "\"");
  }

  @Override
  public Type visitLiteral(LiteralExpr literalExpr) {
    return literalExpr.getValue().getType();
  }

  @Override
  public Type visitVariable(VariableExpr variableExpr) {
    Type varType = variableTypeContext.get(variableExpr.getVariableName());
    if (varType == null) {
      throw new InternalTypeCheckException(
          variableExpr,
          "Don't know type of variable: " + variableExpr.getVariableName());
    } else {
      return varType;
    }
  }

}
