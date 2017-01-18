package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * Created by philipp on 18.01.17.
 */
public class ParseRuntimeException extends RuntimeException {

  private final ParseException parseException;

  public ParseRuntimeException(ParseException parseException) {
    this.parseException = parseException;
  }

  public ParseException getParseException() {
    return parseException;
  }
}
