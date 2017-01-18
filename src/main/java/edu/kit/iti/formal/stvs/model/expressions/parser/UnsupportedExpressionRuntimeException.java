package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * Created by philipp on 18.01.17.
 */
public class UnsupportedExpressionRuntimeException extends RuntimeException {

  private final UnsupportedExpressionException exception;

  public UnsupportedExpressionRuntimeException(String msg) {
    this.exception = new UnsupportedExpressionException(msg);
  }

  public UnsupportedExpressionException getException() {
    return exception;
  }
}
