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

  public CellUnsupportedExpressionProblem(UnsupportedExpressionException exception, String column, int row) {
    super(createErrorMessage(exception), column, row);
    this.exception = exception;
  }

  public UnsupportedExpressionException getUnsupportedExpression() {
    return exception;
  }
}
