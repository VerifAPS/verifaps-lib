package edu.kit.iti.formal.stvs.logic.specification;

/**
 * Created by Philipp on 02.03.2017.
 */
public class ConcretizationException extends Exception {
  private String message;
  private Exception originalException;

  public ConcretizationException(String message) {
    this.message = message;
    originalException = null;
  }

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
