package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * package-local class!
 */
class ParseRuntimeException extends RuntimeException {

  private final ParseException parseException;

  public ParseRuntimeException(ParseException parseException) {
    this.parseException = parseException;
  }

  public ParseException getParseException() {
    return parseException;
  }
}
