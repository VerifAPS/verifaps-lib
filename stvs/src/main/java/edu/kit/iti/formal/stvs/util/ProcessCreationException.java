package edu.kit.iti.formal.stvs.util;

/**
 * An {@link Exception} indicating that an error occurred while attempting to create a process.
 * @author Benjamin Alt
 */
public class ProcessCreationException extends Exception {
  private final String errorMessage;

  public ProcessCreationException(String errorMessage) {
    this.errorMessage = errorMessage;
  }

  @Override
  public String getMessage() {
    return errorMessage;
  }
}
