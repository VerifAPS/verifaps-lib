package edu.kit.iti.formal.stvs.model.expressions;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.IoVariable;

import java.util.Optional;
import java.util.regex.Pattern;

/**
 * runtime-representation for variables in {@link Expression}s.
 * <p>
 * <p>At this point it is not known, whether this is a reference to a
 * {@link FreeVariable}
 * or an {@link IoVariable}, it
 * is simply the String name of either of those.
 *
 * @author Philipp
 */
public class VariableExpr extends Expression {

  public static final Pattern IDENTIFIER_PATTERN = Pattern.compile("[a-zA-Z_][$a-zA-Z0-9_]*");

  private final String varName;
  private final Optional<Integer> index;

  /**
   * Constructs a new VariableExpr with a backwards reference.
   *
   * @param varName the name as a reference to a variable
   * @param index   the index of the backwards-reference
   *                (for expressions like <tt>A[-1]</tt> for example)
   */
  public VariableExpr(String varName, int index) {
    this.varName = varName;
    this.index = Optional.of(index);
  }

  /**
   * Constructs a new VariableExpr without a backwards reference.
   *
   * @param name the name as a reference to a variable.
   */
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
