package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * A runtime exception which indicates the presence of unsupported exceptions in a cell
 * expression (see {@link UnsupportedExpressionException}). This is necessary because ANTLR-based
 * visitors cannot throw checked exceptions - runtime exceptions are unchecked, so this exception
 * should be used in classes derived from ANTLR-generated visitors.
 *
 * @author Philipp
 */
class UnsupportedExpressionRuntimeException extends RuntimeException {

  private final UnsupportedExpressionException exception;

  /**
   * Create a new UnsupportedExpressionRuntimeException with a given message.
   * @param msg The exception message
   */
  public UnsupportedExpressionRuntimeException(String msg) {
    this.exception = new UnsupportedExpressionException(msg);
  }

  public UnsupportedExpressionException getException() {
    return exception;
  }
}
