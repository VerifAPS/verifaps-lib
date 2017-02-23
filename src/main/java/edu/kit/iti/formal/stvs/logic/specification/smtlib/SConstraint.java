package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by csicar on 09.02.17.
 * @author Carsten Csiky
 */
public class SConstraint implements SExpr {
  private final Set<SExpr> globalConstraints;
  private final Set<SExpr> variableDefinitions;

  public SConstraint(Set<SExpr> globalConstraints, Set<SExpr> variableDefinitions) {
    this.globalConstraints = globalConstraints;
    this.variableDefinitions = variableDefinitions;
  }

  public SConstraint() {
    this.globalConstraints = new LinkedHashSet<>();
    this.variableDefinitions = new LinkedHashSet<>();
  }

  public SConstraint combine(RecSConstraint other) {
    addGlobalConstrains(other.getGlobalConstraints());
    addHeaderDefinitions(other.getVariableDefinitions());
    addGlobalConstrains(other.getRecExpression());
    return this;
  }

  public SConstraint combine(SConstraint other) {
    addGlobalConstrains(other.getGlobalConstraints());
    addHeaderDefinitions(other.getVariableDefinitions());
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

  public String headerToText() {
    return getVariableDefinitions().stream()
        .map(SExpr::toText)
        .collect(Collectors.joining(" \n "));
  }

  public String globalConstraintsToText() {
    return getGlobalConstraints().stream()
        .map(constr -> new SList("assert", constr))
        .map(SList::toText)
        .collect(Collectors.joining(" \n "));
  }

  @Override
  public String toText() {
    return headerToText() + " \n " + globalConstraintsToText();
  }

  @Override
  public <E> E visit(SExprVisitor<E> visitor) {
    return visitor.visit(this);
  }

  @Override
  public <E> List<E> visitChildren(SExprVisitor<E> visitor) {
    List<E> result = globalConstraints.stream().map(visitor::visit).collect(Collectors.toList());
    result.addAll(variableDefinitions.stream().map(visitor::visit).collect(Collectors.toList()));
    return result;
  }

  public SConstraint addGlobalConstrains(SExpr ... globalConstraint) {
    return addGlobalConstrains(Arrays.asList(globalConstraint));
  }

  public SConstraint addGlobalConstrains(Collection<SExpr> globalConstraints) {
    this.globalConstraints.addAll(globalConstraints);
    return this;
  }

  public SConstraint addHeaderDefinitions(SExpr ... variableDefinition) {
    return addHeaderDefinitions(Arrays.asList(variableDefinition));
  }

  public SConstraint addHeaderDefinitions(Collection<SExpr> variableDefinitions) {
    this.variableDefinitions.addAll(variableDefinitions);
    return this;
  }

  public Set<SExpr> getGlobalConstraints() {
    return globalConstraints;
  }

  public Set<SExpr> getVariableDefinitions() {
    return variableDefinitions;
  }

  @Override
  public String toString() {
    return "SConstraint{\n" +
        "\tglobalConstraints=\n\t\t" + globalConstraints.stream().map(SExpr::toString).collect
        (Collectors.joining("\n\t\t")) +

        ",\n\n\tvariableDefinitions=\n\t\t" + variableDefinitions.stream().map(SExpr::toString)
        .collect
        (Collectors.joining("\n\t\t")) +
        "\n}";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    SConstraint that = (SConstraint) o;

    if (globalConstraints != null ? !globalConstraints.equals(that.globalConstraints) : that.globalConstraints != null)
      return false;
    return variableDefinitions != null ? variableDefinitions.equals(that.variableDefinitions) : that.variableDefinitions == null;
  }

  @Override
  public int hashCode() {
    int result = globalConstraints != null ? globalConstraints.hashCode() : 0;
    result = 31 * result + (variableDefinitions != null ? variableDefinitions.hashCode() : 0);
    return result;
  }
}
