package edu.kit.iti.formal.stvs.model.common;

import org.apache.commons.lang3.StringEscapeUtils;

import java.util.Collection;
import java.util.Optional;

/**
 * Created by philipp on 09.02.17.
 *
 * @author Philipp
 */
public class DuplicateFreeVariableProblem extends FreeVariableProblem {

  public static Optional<DuplicateFreeVariableProblem> checkForDuplicates(
      FreeVariable freeVariable, Collection<FreeVariable> allVariables) {
    String varName = freeVariable.getName();
    if (isVariableNameAlreadyInCollection(allVariables, varName)) {
      return Optional.of(new DuplicateFreeVariableProblem(varName));
    } else {
      return Optional.empty();
    }
  }

  private static boolean isVariableNameAlreadyInCollection(Collection<FreeVariable> allVariables, String varName) {
    return allVariables.stream()
        .filter(otherVar -> otherVar.getName().equals(varName))
        .count() > 1;
  }

  private DuplicateFreeVariableProblem(String freeVariableName) {
    super("More than one free variable with name "
        + StringEscapeUtils.escapeJava(freeVariableName));
  }

  @Override
  public String getProblemName() {
    return "duplicate variable name";
  }

}
