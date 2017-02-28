package edu.kit.iti.formal.stvs.model.common;

import java.util.Collection;
import java.util.Optional;

import org.apache.commons.lang3.StringEscapeUtils;

/**
 * Created by philipp on 09.02.17.
 *
 * @author Philipp
 */
public class DuplicateFreeVariableProblem extends FreeVariableProblem {

  /**
   * <p>
   * Checks that the given free variable name only occurs once in the given collection, else it
   * returns a {@link DuplicateFreeVariableProblem}.
   * </p>
   *
   * @param freeVariable the free variable to check for duplicates
   * @param allVariables the list of variables that duplicates might be in
   * @return optional of a problem if a duplicate was found or, an empty optional if it wasn't.
   */
  public static Optional<DuplicateFreeVariableProblem> checkForDuplicates(FreeVariable freeVariable,
      Collection<FreeVariable> allVariables) {
    String varName = freeVariable.getName();
    if (isVariableDuplicated(allVariables, varName)) {
      return Optional.of(new DuplicateFreeVariableProblem(varName));
    } else {
      return Optional.empty();
    }
  }

  private static boolean isVariableDuplicated(Collection<FreeVariable> allVariables,
      String varName) {
    return allVariables.stream().filter(otherVar -> otherVar.getName().equals(varName)).count() > 1;
  }

  private DuplicateFreeVariableProblem(String freeVariableName) {
    super(
        "More than one free variable with name " + StringEscapeUtils.escapeJava(freeVariableName));
  }

  @Override
  public String getProblemName() {
    return "duplicate variable name";
  }

}
