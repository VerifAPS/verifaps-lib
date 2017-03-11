package edu.kit.iti.formal.stvs.logic.specification;

/**
 * Exception that gets thrown if concretization fails in general.
 */
public class ConcretizationException extends Exception {
  private String message;
  private Exception originalException;

  public ConcretizationException(String message) {
    this.message = message;
    originalException = null;
  }

  /**
   * Creates an instance by wrapping an existent exception.
   *
   * @param e Exception that causes this exception
   */
  public ConcretizationException(Exception e) {
    super(e);
    originalException = e;
    message = e.getMessage();
  }

  public String getMessage() {
    return message;
  }

  public Exception getOriginalException() {
    return originalException;
  }
}
