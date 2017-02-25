package edu.kit.iti.formal.stvs.logic.specification.smtlib;

/**
 * An {@code SExprVisitor} is used by {@link SExpr} and its subclasses to provide a recursive visiting mechanism.
 * This class can be used to aggregate information of type {@code E} of the visited {@link SExpr}.
 */
@FunctionalInterface
public interface SExprVisitor<E> {
  /**
   * This method gets called when a {@link SExpr} is visited.
   *
   * @param sExpr Expression to visit
   * @return any kind of Information aggregated by this visitor
   */
  E visit(SExpr sExpr);
}
