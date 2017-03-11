package edu.kit.iti.formal.stvs.model.common;

/**
 * A problem concerning {@link FreeVariable}s.
 *
 * @author Philipp
 */
public abstract class FreeVariableProblem extends Exception {

  private final String errorMessage;

  /**
   * Construct a new FreeVariableProblem with a given error message.
   * @param errorMessage The error message
   */
  protected FreeVariableProblem(String errorMessage) {
    this.errorMessage = errorMessage;
  }

  /**
   * Get the error message of this FreeVariableProblem.
   * @return The error message
   */
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
