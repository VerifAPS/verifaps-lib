package edu.kit.iti.formal.stvs.logic.io;

/**
 * Indicates that an exception occurred during exporting.
 *
 * @author Benjamin Alt
 */
public class ExportException extends Exception {
  private String message;
  private Exception originalException;

  public ExportException(String message) {
    this.message = message;
    originalException = null;
  }

  public ExportException(Exception exception) {
    originalException = exception;
    message = exception.getMessage();
  }

  public String getMessage() {
    return message;
  }

  public Exception getOriginalException() {
    return originalException;
  }
}
