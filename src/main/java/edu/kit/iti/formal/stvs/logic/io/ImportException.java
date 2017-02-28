package edu.kit.iti.formal.stvs.logic.io;

/**
 * Indicates that an exception occurred during importing.
 *
 * @author Benjamin Alt
 */
public class ImportException extends Exception {
  private String message;
  private Exception originalException;

  public ImportException(String message) {
    this.message = message;
    originalException = null;
  }

  public ImportException(Exception e) {
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
