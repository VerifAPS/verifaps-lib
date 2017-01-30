package edu.kit.iti.formal.stvs.model.expressions;

/**
 * The runtime-representation for parsed, binary function expressions.
 * Examples are: +, -, =, AND, OR, etc. Anything that has two arguments.
 */
public class BinaryFunctionExpr extends Expression {

  public enum Op {
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

  private final Op operation;
  private final Expression firstArgument;
  private final Expression secondArgument;

  /**
   * @param operation the {@link Op} that this expression should do with its arguments.
   * @param firstArgument the first (or left) argument
   * @param secondArgument the second (or right) argument
   */
  public BinaryFunctionExpr(Op operation, Expression firstArgument, Expression secondArgument) {
    this.operation = operation;
    this.firstArgument = firstArgument;
    this.secondArgument = secondArgument;
  }

  @Override
  public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
    return visitor.visitBinaryFunction(this);
  }

  public Op getOperation() {
    return operation;
  }

  public Expression getFirstArgument() {
    return firstArgument;
  }

  public Expression getSecondArgument() {
    return secondArgument;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof BinaryFunctionExpr)) return false;

    BinaryFunctionExpr that = (BinaryFunctionExpr) o;

    if (operation != that.operation) {
      return false;
    }
    if (firstArgument != null ? !firstArgument.equals(that.firstArgument) : that.firstArgument != null) {
      return false;
    }
    return secondArgument != null ? secondArgument.equals(that.secondArgument) : that.secondArgument == null;
  }

  @Override
  public int hashCode() {
    int result = operation != null ? operation.hashCode() : 0;
    result = 31 * result + (firstArgument != null ? firstArgument.hashCode() : 0);
    result = 31 * result + (secondArgument != null ? secondArgument.hashCode() : 0);
    return result;
  }

  public String toString() {
    return "Bin(" + firstArgument + " " + operation + " " + secondArgument + ")";
  }
}
