package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by csicar on 09.02.17.
 */
public class SConstrain extends SList {
  private List<SExpr> variableDefinitions;
  private List<SExpr> sideConditions;

  public SConstrain() {
    super();
    variableDefinitions = new LinkedList<>();
    sideConditions = new LinkedList<>();
  }

  public SConstrain(List<SExpr> constraints) {
    super(constraints);
  }

  public SConstrain addSideConditions(List<SExpr> sideConditions) {
    sideConditions.addAll(sideConditions);
    return this;
  }

  public SConstrain addSideConditions(SExpr ... sideConditions) {
    return addSideConditions(Arrays.asList(sideConditions));
  }


  public SConstrain addVariableDefinition(List<SExpr> variableDefinitions) {
    variableDefinitions.addAll(variableDefinitions);
    return this;
  }

  public SConstrain addVariableDefinition(SExpr ... variableDefinitions) {
    return addVariableDefinition(Arrays.asList(variableDefinitions));
  }
}
