package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;

/**
 * An instance is created when an {@link Expression} in a {@link ConstraintCell} is ill-typed.
 *
 * @author Benjamin Alt
 */
public class CellTypeProblem extends CellProblem {

  /**
   * <p>
   * Either the given expression is well-typed and evaluates to a boolean and is returned, or a
   * {@link CellTypeProblem} is thrown.
   * </p>
   *
   * @param typeChecker type checker for checking the type of this cell
   * @param columnId the column of the expression to check
   * @param row the row of the expression to check
   * @param expr the expression to type-check for illness / not evaluating to boolean
   * @return an expression that <strong>must</strong> evaluate to true
   * @throws CellTypeProblem a problem if the expression does not evaluate to a boolean or is
   *         ill-typed
   */
  public static Expression tryTypeCheckCellExpression(TypeChecker typeChecker, String columnId,
      int row, Expression expr) throws CellTypeProblem {
    try {
      Type type = typeChecker.typeCheck(expr);
      if (type.checksAgainst(TypeBool.BOOL)) {
        return expr;
      } else {
        throw new CellTypeProblem(
            new TypeCheckException(expr, "The cell expression must evaluate to a boolean, "
                + "instead it evaluates to: " + type.getTypeName()),
            columnId, row);
      }
    } catch (TypeCheckException typeCheckException) {
      throw new CellTypeProblem(typeCheckException, columnId, row);
    }
  }

  private static String createErrorMessage(TypeCheckException exception) {
    return exception.getMessage();
  }

  private final TypeCheckException exception;

  /**
   * Create a new CellTypeProblem for a given {@link TypeCheckException}, a column and a row.
   * @param exception The underlying exception
   * @param column The column of the problematic cell
   * @param row The row of the problematic cell
   */
  public CellTypeProblem(TypeCheckException exception, String column, int row) {
    super(createErrorMessage(exception), column, row);
    this.exception = exception;
  }

  public TypeCheckException getTypeCheckException() {
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

    CellTypeProblem that = (CellTypeProblem) obj;

    return exception != null ? exception.equals(that.exception) : that.exception == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (exception != null ? exception.hashCode() : 0);
    return result;
  }
}
