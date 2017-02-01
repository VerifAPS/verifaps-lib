package edu.kit.iti.formal.stvs.model.expressions;

import edu.kit.iti.formal.stvs.model.common.IoVariable;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;

/**
 * The abstract super-class for all Expressions.
 *
 * <p>This type does not contain all information the source
 * expression string had. That means you can't get back the
 * expression string from this Expression. For example an expression
 * <tt>= 3</tt> in a column for {@link IoVariable}
 * <tt>X</tt> is parsed as <tt>X = 3</tt> by the
 * {@link ExpressionParser}.
 *
 * <p>The only ability all Expressions currently share is
 * getting visited.
 */
public abstract class Expression {

  /**
   * Find out what subclass of Expression this is by supplying
   * a visitor.
   * @param visitor an {@link ExpressionVisitor} for handling different
   *                cases of Expression sublcasses
   * @param <R> the return type that the expression visitor produces
   * @return the return value that the expression visitor produced
   */
  public abstract <R> R takeVisitor(ExpressionVisitor<R> visitor);

}
