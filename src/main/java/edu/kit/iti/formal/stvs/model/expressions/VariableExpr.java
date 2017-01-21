package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Optional;

public class VariableExpr extends Expression {

  private final String varName;
  private final Optional<Integer> index;

  public VariableExpr(String varName, Optional<Integer> index) {
    this.varName = varName;
    this.index = index;
  }

  public VariableExpr(String name) {
    this.varName = name;
    this.index = Optional.empty();
  }

  @Override
  public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
    return visitor.visitVariable(this);
  }

  public String getVariableName() {
    return varName;
  }

  public Optional<Integer> getIndex() {
    return index;
  }

  public boolean equals(VariableExpr expr) {
    return getVariableName().equals(expr.getVariableName());
  }

  @Override
  public boolean equals(Object other) {
    return (other instanceof VariableExpr) && this.equals((VariableExpr) other);
  }

  public String toString() {
    String indexStr = index.map(i -> "[" + i + "]").orElse("");
    return "VariableExpr(" + varName + indexStr + ")";
  }

}
