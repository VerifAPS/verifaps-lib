package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by csicar on 09.02.17.
 */
public class SConstrain implements SExpr {
  private List<SExpr> variableDefinitions;
  private List<SExpr> sideConditions;
  private List<SExpr> userConditions;

  public SConstrain(List<SExpr> userConditions, List<SExpr> variableDefinitions, List<SExpr>
      sideConditions) {
    this.variableDefinitions = variableDefinitions;

    this.sideConditions = sideConditions;
    this.userConditions = userConditions;
  }

  public SConstrain(List<SExpr> userConditions) {
    this(userConditions, new LinkedList<SExpr>(), new LinkedList<>());
  }

  public SConstrain() {
    this(new LinkedList<>());
  }

  @Override
  public boolean isAtom() {
    return false;
  }


  public SList toSingleExpression() {
    List<SExpr> complete = new ArrayList<>(variableDefinitions);
    complete.addAll(sideConditions);
    complete.addAll(userConditions);
    return new SList(complete);
  }

  @Override
  public Sexp toSexpr() {
    return toSingleExpression().toSexpr();
  }

  public SConstrain addAllUserConditions(List<SExpr> userConditions) {
    this.userConditions.addAll(userConditions);
    return this;
  }

  public SConstrain addAllUserConditions(SList userConditions) {
    return addAllUserConditions(userConditions.getList());
  }

  public SConstrain addAllSideConditions(SExpr ... sideConditions) {
    return addAllSideConditions(Arrays.asList(sideConditions));
  }

  public SConstrain addAllSideConditions(List<SExpr> sideConditions) {
    this.sideConditions.addAll(sideConditions);
    return this;
  }

  public SConstrain addAllVariableDefinitions(SExpr ... variableDefinitions) {
    return addAllVariableDefinitions(Arrays.asList(variableDefinitions));
  }

  public SConstrain addAllVariableDefinitions(List<SExpr> variableDefinitions) {
    this.variableDefinitions.addAll(variableDefinitions);
    return this;
  }

  public List<SExpr> getVariableDefinitions() {
    return variableDefinitions;
  }

  public List<SExpr> getSideConditions() {
    return sideConditions;
  }

  public List<SExpr> getUserConditions() {
    return userConditions;
  }

  /**
   * get userexpression anded together
   * @return
   */
  public SExpr getUserConditionAsSingleExpression() {
    return new SList("and").addAll(userConditions);
  }
}
