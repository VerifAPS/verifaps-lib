package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException;

/**
 * @author Benjamin Alt
 */
public class CellTypeProblem extends CellProblem {

  private static String createErrorMessage(TypeCheckException exception) {
    return exception.getMessage();
  }

  private final TypeCheckException exception;

  public CellTypeProblem(TypeCheckException exception, String column, int row) {
    super(createErrorMessage(exception), column, row);
    this.exception = exception;
  }

  public TypeCheckException getTypeCheckException() {
    return exception;
  }

}
