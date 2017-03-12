package edu.kit.iti.formal.stvs.logic.io;

/**
 * Indicates that an exception occurred during importing.
 *
 * @author Benjamin Alt
 */
public class ImportException extends Exception {
  private String message;
  private Exception originalException;

  /**
   * Create a new ImportException with a given error message.
   * @param message The error message
   */
  public ImportException(String message) {
    this.message = message;
    originalException = null;
  }

  /**
   * Create a new ImportException from a given Exception (e.g. an exception which was caught
   * during import).
   * @param e The original exception
   */
  public ImportException(Exception e) {
    originalException = e;
    message = e.getMessage();
  }

  /**
   * Get the error message of this ImportException.
   * @return The error message
   */
  public String getMessage() {
    return message;
  }
}
