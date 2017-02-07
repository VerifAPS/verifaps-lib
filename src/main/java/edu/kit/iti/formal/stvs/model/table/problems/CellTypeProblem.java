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

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    CellTypeProblem that = (CellTypeProblem) o;

    return exception != null ? exception.equals(that.exception) : that.exception == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (exception != null ? exception.hashCode() : 0);
    return result;
  }
}
