package edu.kit.iti.formal.stvs.model.expressions;

/**
 * An Exception for type errors. Occurs when one wants to parse an {@link Expression} like
 * <tt>2 AND TRUE</tt> or <tt>42 = FALSE</tt>.
 *
 * @author Philipp
 */
public class TypeCheckException extends Exception {
  private static final long serialVersionUID = 1L;

  private final Expression mistypedExpression;

  /**
   * @param mistypedExpression the expression that is ill-typed. This would be the whole expression
   *        (for example <tt>2 AND TRUE</tt>)
   * @param message a message about what went wrong.
   */
  public TypeCheckException(Expression mistypedExpression, String message) {
    super(message + "\nIn Expression: " + mistypedExpression);
    this.mistypedExpression = mistypedExpression;
  }

  /**
   * @return the expression that is ill-typed. This would be the whole expression (for example
   *         <tt>2 AND TRUE</tt>)
   */
  public Expression getMistypedExpression() {
    return mistypedExpression;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    TypeCheckException that = (TypeCheckException) o;

    return getMistypedExpression() != null
        ? getMistypedExpression().equals(that.getMistypedExpression())
        : that.getMistypedExpression() == null;
  }
}
