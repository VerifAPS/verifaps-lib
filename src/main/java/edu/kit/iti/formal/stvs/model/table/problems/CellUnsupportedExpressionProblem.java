package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;

/**
 * <p>The cell problem analogue to the {@link UnsupportedExpressionException}. Created when
 * expressions with function calls or if guards or similar are encountered, that have not yet
 * been implemented.</p>
 *
 * @author Benjamin Alt
 */
public class CellUnsupportedExpressionProblem extends CellProblem {

  private final UnsupportedExpressionException exception;

  private static String createErrorMessage(UnsupportedExpressionException exception) {
    return exception.getMessage();
  }

  /**
   * <p>Creates the cell problem for an {@link UnsupportedExpressionException}.</p>
   *
   * @param exception the exception that caused this cell problem
   * @param column the column of the cell in the table
   * @param row the row of the cell in the table
   */
  public CellUnsupportedExpressionProblem(
      UnsupportedExpressionException exception, String column, int row) {
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
