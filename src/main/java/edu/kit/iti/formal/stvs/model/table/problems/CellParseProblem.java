package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;

import java.util.List;

/**
 * @author Benjamin Alt
 */
public class CellParseProblem extends CellProblem {

  private final ParseException exception;

  public static Expression expressionOrProblemForCell(List<Type> typeContext, TypeChecker typeChecker, String columnId, int row, ConstraintCell cell)
      throws CellProblem {
    try {
      return CellTypeProblem.createValidExpressionFromCell(typeContext, typeChecker, columnId, cell);
    } catch (TypeCheckException typeCheckException) {
      throw new CellTypeProblem(typeCheckException, columnId, row);
    } catch (ParseException parseException) {
      throw new CellParseProblem(parseException, columnId, row);
    } catch (UnsupportedExpressionException unsupportedException) {
      throw new CellUnsupportedExpressionProblem(unsupportedException, columnId, row);
    }
  }

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
