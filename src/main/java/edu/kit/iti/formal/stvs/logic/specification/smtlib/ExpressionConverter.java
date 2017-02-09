package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.expressions.Expression;

/**
 * Created by csicar on 09.02.17.
 */
public class ExpressionConverter {
  private final Expression expression;
  private final List<>
  private final int z;


  public ExpressionConverter(Expression expression, int z) {
    this.z = z;
    this.expression = expression;
  }

  /**
   * applies the Rule A[-α] -> A_z_i[-α]
   * this is part of rule IV
   * and the Rule A_z_i[-α] -> A_z_(i-α)
   * this is part of rule II
   * @param i iteration of the row (i-th unrolling)
   * @return the to smtlib-sexpr converted expression
   */
  public SExpr convert(int i) {
    return null;
  }
}
