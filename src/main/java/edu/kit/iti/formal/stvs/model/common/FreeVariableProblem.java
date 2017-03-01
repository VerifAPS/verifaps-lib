package edu.kit.iti.formal.stvs.model.common;

/**
 * Created by philipp on 09.02.17.
 *
 * @author Philipp
 */
public abstract class FreeVariableProblem extends Exception {

  private final String errorMessage;

  protected FreeVariableProblem(String errorMessage) {
    this.errorMessage = errorMessage;
  }

  public String getErrorMessage() {
    return errorMessage;
  }

  /**
   * <p>This method can be used for showing text in the gui.</p>
   *
   * @return a message suited for a dialog in the view
   */
  public String getGuiMessage() {
    return getProblemName() + ": " + getErrorMessage();
  }

  public abstract String getProblemName();

}
