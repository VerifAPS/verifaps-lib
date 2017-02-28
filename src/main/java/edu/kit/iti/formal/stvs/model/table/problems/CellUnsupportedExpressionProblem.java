package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;

/**
 * @author Benjamin Alt
 */
public class CellUnsupportedExpressionProblem extends CellProblem {

  private final UnsupportedExpressionException exception;

  private static String createErrorMessage(UnsupportedExpressionException exception) {
    return exception.getMessage();
  }

  public CellUnsupportedExpressionProblem(UnsupportedExpressionException exception, String column,
      int row) {
    super(createErrorMessage(exception), column, row);
    this.exception = exception;
  }

  public UnsupportedExpressionException getUnsupportedExpression() {
    return exception;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }
    if (!super.equals(obj)) {
      return false;
    }

    CellUnsupportedExpressionProblem that = (CellUnsupportedExpressionProblem) obj;

    return exception != null ? exception.equals(that.exception) : that.exception == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (exception != null ? exception.hashCode() : 0);
    return result;
  }
}
