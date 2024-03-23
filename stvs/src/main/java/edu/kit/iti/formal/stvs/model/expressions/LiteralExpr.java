package edu.kit.iti.formal.stvs.model.expressions;

/**
 * The class for expressions that are constant. Examples are <tt>42</tt>, <tt>TRUE</tt> or
 * <tt>my_enum_constructor</tt>.
 *
 * @author Philipp
 */
public class LiteralExpr extends Expression {

  private final Value value;

  /**
   * @param val the runtime-representation for values that this literal is.
   */
  public LiteralExpr(Value val) {
    this.value = val;
  }

  @Override
  public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
    return visitor.visitLiteral(this);
  }

  public Value getValue() {
    return value;
  }

  public boolean equals(LiteralExpr expr) {
    return getValue().equals(expr.getValue());
  }

  @Override
  public boolean equals(Object other) {
    return (other instanceof LiteralExpr) && this.equals((LiteralExpr) other);
  }

  @Override
  public int hashCode() {
    return getValue() != null ? getValue().hashCode() : 0;
  }

  @Override
  public String toString() {
    return "LiteralExpr(" + value + ")";
  }
}
