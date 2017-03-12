package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * A runtime exception which indicates errors during parsing. This is necessary because ANTLR-based
 * visitors cannot throw checked exceptions - runtime exceptions are unchecked, so this exception
 * should be used in classes derived from ANTLR-generated visitors.
 *
 * @author Philipp
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
