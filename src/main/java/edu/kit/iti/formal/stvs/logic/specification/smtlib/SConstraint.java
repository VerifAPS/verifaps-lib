package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Represents sets of constraints and definitions.
 *
 * @author Carsten Csiky
 */
public class SConstraint implements SExpr {
  private final Set<SExpr> globalConstraints;
  private final Set<SExpr> variableDefinitions;

  /**
   * Creates an instance with preset definitions/constraints.
   *
   * @param globalConstraints   set of global constraints
   * @param variableDefinitions set of variable definitions
   */
  public SConstraint(Set<SExpr> globalConstraints, Set<SExpr> variableDefinitions) {
    this.globalConstraints = globalConstraints;
    this.variableDefinitions = variableDefinitions;
  }

  /**
   * Creates an instance with empty sets.
   */
  public SConstraint() {
    this.globalConstraints = new LinkedHashSet<>();
    this.variableDefinitions = new LinkedHashSet<>();
  }

  /**
   * Adds all constraints and definitions of {@code other} to this object.
   *
   * @param other object from which the constraints/definitions should be taken
   * @return this (now with added constraints/definitions)
   */
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

  /**
   * Converts all definitions to text compatible with smt definitions.
   *
   * @return definitions as string
   */
  public String headerToText() {
    return getVariableDefinitions().stream()
        .map(SExpr::toText)
        .collect(Collectors.joining(" \n "));
  }

  /**
   * Converts all global constraints to text compatible with smt.
   *
   * @return constraints as string
   */
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

  public SConstraint addGlobalConstrains(SExpr... globalConstraint) {
    return addGlobalConstrains(Arrays.asList(globalConstraint));
  }

  public SConstraint addGlobalConstrains(Collection<SExpr> globalConstraints) {
    this.globalConstraints.addAll(globalConstraints);
    return this;
  }

  public SConstraint addHeaderDefinitions(SExpr... variableDefinition) {
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
    return "SConstraint{\n"
        + "\tglobalConstraints=\n\t\t" + globalConstraints.stream().map(SExpr::toString).collect(
            Collectors.joining("\n\t\t"))
        + ",\n\n\tvariableDefinitions=\n\t\t" + variableDefinitions.stream().map(SExpr::toString)
        .collect(Collectors.joining("\n\t\t")) + "\n}";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SConstraint that = (SConstraint) o;

    if (globalConstraints != null
        ? !globalConstraints.equals(that.globalConstraints)
        : that.globalConstraints != null) {
      return false;
    }
    return variableDefinitions != null
        ? variableDefinitions.equals(that.variableDefinitions)
        : that.variableDefinitions == null;
  }

  @Override
  public int hashCode() {
    int result = globalConstraints != null ? globalConstraints.hashCode() : 0;
    result = 31 * result + (variableDefinitions != null ? variableDefinitions.hashCode() : 0);
    return result;
  }
}
