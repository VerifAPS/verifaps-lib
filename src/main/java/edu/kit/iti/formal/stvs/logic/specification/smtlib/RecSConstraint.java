package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import java.util.Set;

/**
 * Created by csicar on 09.02.17.
 */
public class RecSConstraint extends SConstraint {
  private SExpr recExpression;

  public RecSConstraint(SExpr recExpression) {
    super();
    this.recExpression = recExpression;
  }

  public RecSConstraint(SExpr recExpression, Set<SExpr> globalConstraints, Set<SExpr>
      variableDefinitions) {
    super(globalConstraints, variableDefinitions);
    this.recExpression = recExpression;
  }

  public RecSConstraint combineWith(String operator, RecSConstraint ... operands) {
    SList list = new SList(operator).addAll(recExpression).addAll(operands);
    this.recExpression = list;
    for (RecSConstraint operand : operands) {
      addGlobalConstrains(operand.getGlobalConstraints());
      addHeaderDefinitions(operand.getVariableDefinitions());
    }
    return this;
  }

  public SConstraint combine(SConstraint other) {
    return other.combine(this);
  }

  public SExpr getRecExpression() {
    return recExpression;
  }
}