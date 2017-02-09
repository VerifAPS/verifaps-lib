package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;

import java.util.*;

/**
 * Created by csicar on 09.02.17.
 */
public class SConstraint implements SExpr {
  private final Set<SExpr> globalConstraints;
  private final Set<SExpr> variableDefinitions;

  public SConstraint(Set<SExpr> globalConstraints, Set<SExpr> variableDefinitions) {
    this.globalConstraints = globalConstraints;
    this.variableDefinitions = variableDefinitions;
  }

  public SConstraint() {
    this.globalConstraints = new HashSet<>();
    this.variableDefinitions = new HashSet<>();
  }

  public SConstraint combine(RecSConstraint other) {
    addGlobalConstrains(other.getGlobalConstraints());
    addVariableDefinitions(other.getVariableDefinitions());
    addGlobalConstrains(other.getRecExpression());
    return this;
  }

  public SConstraint combine(SConstraint other) {
    addGlobalConstrains(other.getGlobalConstraints());
    addVariableDefinitions(other.getVariableDefinitions());
    return this;
  }

  @Override
  public boolean isAtom() {
    return false;
  }

  @Override
  public Sexp toSexpr() {
    return null;
  }

  public SConstraint addGlobalConstrains(SExpr ... globalConstraint) {
    return addGlobalConstrains(Arrays.asList(globalConstraint));
  }

  public SConstraint addGlobalConstrains(Collection<SExpr> globalConstraints) {
    this.globalConstraints.addAll(globalConstraints);
    return this;
  }

  public SConstraint addVariableDefinitions(SExpr ... variableDefinition) {
    return addVariableDefinitions(Arrays.asList(variableDefinition));
  }

  public SConstraint addVariableDefinitions(Collection<SExpr> variableDefinitions) {
    this.variableDefinitions.addAll(variableDefinitions);
    return this;
  }

  public Set<SExpr> getGlobalConstraints() {
    return globalConstraints;
  }

  public Set<SExpr> getVariableDefinitions() {
    return variableDefinitions;
  }
}
