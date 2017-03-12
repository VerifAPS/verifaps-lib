package edu.kit.iti.formal.stvs.logic.io;

/**
 * Indicates that an error occurred during exporting.
 *
 * @author Benjamin Alt
 */
public class ExportException extends Exception {
  private String message;
  private Exception originalException;

  /**
   * Create a new ExportException with a given error message.
   * @param message The error message
   */
  public ExportException(String message) {
    this.message = message;
    originalException = null;
  }

  /**
   * Create a new ExportException from an exception (e.g. an exception that was thrown and caught
   * during export).
   * @param exception The original exception
   */
  public ExportException(Exception exception) {
    originalException = exception;
    message = exception.getMessage();
  }

  /**
   * Get the error message of this ExportException.
   * @return The error message
   */
  public String getMessage() {
    return message;
  }
}
