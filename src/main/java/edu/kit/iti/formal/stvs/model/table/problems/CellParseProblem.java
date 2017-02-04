package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;

/**
 * @author Benjamin Alt
 */
public class CellParseProblem extends CellProblem {

  private final ParseException exception;

  private static String createErrorMessage(ParseException exception) {
    return exception.getMessage();
  }

  public CellParseProblem(ParseException exception, String column, int row) {
    super(createErrorMessage(exception), column, row);
    this.exception = exception;
  }

  public ParseException getParseException() {
    return exception;
  }
}
