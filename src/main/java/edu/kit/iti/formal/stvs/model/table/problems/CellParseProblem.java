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

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    CellParseProblem that = (CellParseProblem) o;

    return exception != null ? exception.equals(that.exception) : that.exception == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (exception != null ? exception.hashCode() : 0);
    return result;
  }

  public ParseException getParseException() {
    return exception;
  }
}
