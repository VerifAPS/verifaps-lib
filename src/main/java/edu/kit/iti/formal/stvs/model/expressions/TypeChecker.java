package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Map;

/**
 * A type checker for {@link Expression}s.
 * <p>
 * If an ill-typed expression is encountered, this class produces a {@link TypeCheckException}.
 *
 * @author Philipp
 */
public class TypeChecker implements ExpressionVisitor<Type> {

  private static class InternalTypeCheckException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    private final Expression mistypedExpression;

    InternalTypeCheckException(Expression mistypedExpression, String message) {
      super(message);
      this.mistypedExpression = mistypedExpression;
    }

    Expression getMistypedExpression() {
      return mistypedExpression;
    }

  }

  private final Map<String, Type> variableTypeContext;

  /**
   * Since the {@link Expression} AST does not know about the type of a variable (see
   * {@link VariableExpr}), this class needs a type context for variables.
   * <p>
   * The type checker does not handle free- or IoVariables differently. Both are reduced to their
   * string representation.
   *
   * @param variableTypeContext a map from variable names to types.
   */
  public TypeChecker(Map<String, Type> variableTypeContext) {
    this.variableTypeContext = variableTypeContext;
  }

  /**
   * Checks the type of an {@link Expression} or throws a {@link TypeCheckException} on an ill-typed
   * expression.
   *
   * @param expr the expression to be checked
   * @return the type of the expression, iff not ill-typed.
   * @throws TypeCheckException an exception with information about the type error, if an ill-typed
   *         expression is encountered
   */
  public Type typeCheck(Expression expr) throws TypeCheckException {
    try {
      return expr.takeVisitor(this);
    } catch (InternalTypeCheckException runtimeException) {
      throw new TypeCheckException(runtimeException.getMistypedExpression(),
          runtimeException.getMessage());
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
        return throwUnkownOperation(binaryFunctionExpr.getOperation().toString(),
            binaryFunctionExpr);
    }
  }

  private void assertTypeEquality(Type expectedType, Type actualType, Expression expr) {
    if (!actualType.checksAgainst(expectedType)) {
      throw new InternalTypeCheckException(expr, "Expected type \"" + expectedType.getTypeName()
          + "\"," + "but got \"" + actualType.getTypeName() + "\"");
    }
  }

  // Almost Only differs in error message from assertTypeEquality
  private void assertEqualTypes(Type type1, Type type2, Expression expr) {
    if (!type1.equals(type2)) {
      throw new InternalTypeCheckException(expr,
          "Expected equal types, but got 2 different types: \"" + type1.getTypeName() + "\""
              + " and \"" + type2.getTypeName() + "\"");
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
      throw new InternalTypeCheckException(variableExpr,
          "Don't know type of variable: " + variableExpr.getVariableName());
    } else {
      return varType;
    }
  }

}
