package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Represents sets of constraints and definitions.
 *
 * @author Carsten Csiky
 */
public class SmtModel implements SExpression {
  private final List<SExpression> globalConstraints;
  private final List<SExpression> variableDefinitions;

  /**
   * Creates an instance with preset definitions/constraints.
   * both lists should be modifiable
   * @param globalConstraints set of global constraints
   * @param variableDefinitions set of variable definitions
   */
  public SmtModel(List<SExpression> globalConstraints, List<SExpression> variableDefinitions) {
    this.globalConstraints = globalConstraints;
    this.variableDefinitions = variableDefinitions;
  }

  /**
   * Creates an instance with empty sets.
   */
  public SmtModel() {
    this.globalConstraints = new ArrayList<>();
    this.variableDefinitions = new ArrayList<>();
  }

  /**
   * Adds all constraints and definitions of {@code other} to this object.
   *
   * @param other object from which the constraints/definitions should be taken
   * @return this (now with added constraints/definitions)
   */
  public SmtModel combine(SmtModel other) {
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

    SList equivalentSList = new SList().addAll(getVariableDefinitions());
    getGlobalConstraints().forEach((constraint) -> equivalentSList.addAll(new SList("assert",
        constraint)));
    return equivalentSList.toSexpr();
  }

  /**
   * Converts all definitions to text compatible with smt definitions.
   *
   * @return definitions as string
   */
  public String headerToText() {
    return getVariableDefinitions().stream().map(SExpression::toText)
        .collect(Collectors.joining(" \n "));
  }

  /**
   * Converts all global constraints to text compatible with smt.
   *
   * @return constraints as string
   */
  public String globalConstraintsToText() {
    return getGlobalConstraints().stream().map(constr -> new SList("assert", constr))
        .map(SList::toText).collect(Collectors.joining(" \n "));
  }

  @Override
  public String toText() {
    return headerToText() + " \n " + globalConstraintsToText();
  }

  public SmtModel addGlobalConstrains(SExpression... globalConstraint) {
    return addGlobalConstrains(Arrays.asList(globalConstraint));
  }

  public SmtModel addGlobalConstrains(Collection<SExpression> globalConstraints) {
    this.globalConstraints.addAll(globalConstraints);
    return this;
  }

  public SmtModel addHeaderDefinitions(SExpression... variableDefinition) {
    return addHeaderDefinitions(Arrays.asList(variableDefinition));
  }

  public SmtModel addHeaderDefinitions(Collection<SExpression> variableDefinitions) {
    this.variableDefinitions.addAll(variableDefinitions);
    return this;
  }

  public List<SExpression> getGlobalConstraints() {
    return globalConstraints;
  }

  public List<SExpression> getVariableDefinitions() {
    return variableDefinitions;
  }

  @Override
  public String toString() {
    return "SmtModel{\n" + "\tglobalConstraints=\n\t\t"
        + globalConstraints.stream().map(SExpression::toString)
            .collect(Collectors.joining("\n\t\t"))
        + ",\n\n\tvariableDefinitions=\n\t\t" + variableDefinitions.stream()
            .map(SExpression::toString).collect(Collectors.joining("\n\t\t"))
        + "\n}";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SmtModel that = (SmtModel) o;

    if (globalConstraints != null ? !globalConstraints.equals(that.globalConstraints)
        : that.globalConstraints != null) {
      return false;
    }
    return variableDefinitions != null ? variableDefinitions.equals(that.variableDefinitions)
        : that.variableDefinitions == null;
  }

  @Override
  public int hashCode() {
    int result = globalConstraints != null ? globalConstraints.hashCode() : 0;
    result = 31 * result + (variableDefinitions != null ? variableDefinitions.hashCode() : 0);
    return result;
  }
}
