package edu.kit.iti.formal.stvs.model.expressions;

public class LiteralExpr extends Expression {

  private final Value value;

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

  public String toString() {
    return "LiteralExpr(" + value + ")";
  }

}
