package edu.kit.iti.formal.stvs.model.expressions;

import java.util.List;

public class FunctionExpr extends Expression {

  public static enum Operation {
    // BOOL -> BOOL
    NOT,
    // INT -> INT
    UNARY_MINUS,
    // (BOOL, BOOL) -> BOOL
    AND,
    OR,
    XOR,
    // (INT, INT) -> BOOL
    GREATER_THAN,
    GREATER_EQUALS,
    LESS_THAN,
    LESS_EQUALS,
    // (a, a) -> BOOL
    EQUALS,
    NOT_EQUALS,
    // (INT, INT) -> INT
    PLUS,
    MINUS,
    MULTIPLICATION,
    DIVISION,
    MODULO,
    POWER
  }

  private final Operation operation;
  private final List<Expression> arguments;

  public FunctionExpr(Operation op, List<Expression> arguments) {
    this.operation = op;
    this.arguments = arguments;
  }

  @Override
  public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
    return visitor.visitFunctionExpr(this);
  }

  public Operation getOperation() {
    return operation;
  }

  public List<Expression> getArguments() {
    return arguments;
  }

  public boolean equals(FunctionExpr expr) {
    return getOperation().equals(expr.getOperation())
        && getArguments().equals(expr.getArguments());
  }

  @Override
  public boolean equals(Object other) {
    return (other instanceof FunctionExpr) && this.equals((FunctionExpr) other);
  }

  public String toString() {
    return "FunctionExpr(" + operation + ", " + arguments + ")";
  }

}
