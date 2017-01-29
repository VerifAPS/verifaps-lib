package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * package-local class!
 */
class UnsupportedExpressionRuntimeException extends RuntimeException {

  private final UnsupportedExpressionException exception;

  public UnsupportedExpressionRuntimeException(String msg) {
    this.exception = new UnsupportedExpressionException(msg);
  }

  public UnsupportedExpressionException getException() {
    return exception;
  }
}
