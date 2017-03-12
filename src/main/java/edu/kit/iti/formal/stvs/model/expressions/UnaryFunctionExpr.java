package edu.kit.iti.formal.stvs.model.expressions;

/**
 * Runtime-representation of unary expressions. Examples: <tt>NOT TRUE</tt>, <tt>- 3</tt>.
 *
 * @author Philipp
 */
public class UnaryFunctionExpr extends Expression {

  public enum Op {
    // BOOL -> BOOL
    NOT,
    // INT -> INT
    UNARY_MINUS,
  }

  private final Op operation;
  private final Expression argument;

  /**
   * Creates an instance that represents an unary function.
   *
   * @param operation the unary operation
   * @param argument the expression to apply the operation to
   */
  public UnaryFunctionExpr(Op operation, Expression argument) {
    this.operation = operation;
    this.argument = argument;
  }

  @Override
  public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
    return visitor.visitUnaryFunction(this);
  }

  public Op getOperation() {
    return operation;
  }

  public Expression getArgument() {
    return argument;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (!(o instanceof UnaryFunctionExpr)) {
      return false;
    }

    UnaryFunctionExpr that = (UnaryFunctionExpr) o;

    if (operation != that.operation) {
      return false;
    }
    return argument != null ? argument.equals(that.argument) : that.argument == null;
  }

  @Override
  public int hashCode() {
    int result = operation != null ? operation.hashCode() : 0;
    result = 31 * result + (argument != null ? argument.hashCode() : 0);
    return result;
  }

  public String toString() {
    return "Unary(" + operation + " " + argument + ")";
  }
}
