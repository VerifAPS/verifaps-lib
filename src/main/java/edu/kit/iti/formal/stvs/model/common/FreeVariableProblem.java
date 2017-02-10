package edu.kit.iti.formal.stvs.model.common;

/**
 * Created by philipp on 09.02.17.
 */
public abstract class FreeVariableProblem extends Exception {

  private final String errorMessage;

  protected FreeVariableProblem(String errorMessage) {
    this.errorMessage = errorMessage;
  }

  public String getErrorMessage() {
    return errorMessage;
  }
}
