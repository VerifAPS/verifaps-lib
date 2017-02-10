package edu.kit.iti.formal.stvs.model.common;

import org.apache.commons.lang3.StringEscapeUtils;

import java.util.Collection;
import java.util.Optional;

/**
 * Created by philipp on 09.02.17.
 */
public class DuplicateFreeVariableProblem extends FreeVariableProblem {

  public static Optional<DuplicateFreeVariableProblem> checkForDuplicates(
      FreeVariable freeVariable, Collection<FreeVariable> allVariables) {
    String varName = freeVariable.getName();
    if (allVariables.stream().filter(otherVar -> otherVar.getName().equals(varName)).count() > 1) {
      return Optional.of(new DuplicateFreeVariableProblem(varName));
    } else {
      return Optional.empty();
    }
  }

  private DuplicateFreeVariableProblem(String freeVariableName) {
    super("More than one free variable with name "
        + StringEscapeUtils.escapeJava(freeVariableName));
  }

}
