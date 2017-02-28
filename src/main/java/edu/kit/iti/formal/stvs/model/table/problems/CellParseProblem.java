package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;

import java.util.List;

/**
 * <p>A problem that is generated when a ConstraintCell inside a Constraint/HybridSpecification
 * cannot be parsed correctly (i.e. according to the antlr grammar file in <tt>src/main/antlr</tt>)
 * </p>
 *
 * @author Benjamin Alt
 */
public class CellParseProblem extends CellProblem {

  /**
   * <p>Tries to create an {@link Expression} from the given string and context information.</p>
   *
   * @param typeContext the type context needed for parsing enums
   * @param columnId the column of the cell to check
   * @param row the row of the cell to check
   * @param cell the cell to parse
   * @return an {@link Expression}-AST (that might still be ill-typed)
   * @throws CellParseProblem if the expression could not be parsed
   * @throws CellUnsupportedExpressionProblem if the expression contains unsupported grammar
   *                                          features (for example function calls)
   */
  public static Expression tryParseCellExpression(
      List<Type> typeContext, String columnId, int row, ConstraintCell cell)
      throws CellParseProblem, CellUnsupportedExpressionProblem {
    ExpressionParser parser = new ExpressionParser(columnId, typeContext);
    try {
      return parser.parseExpression(cell.getAsString());
    } catch (ParseException parseException) {
      throw new CellParseProblem(parseException, columnId, row);
    } catch (UnsupportedExpressionException unsupportedException) {
      throw new CellUnsupportedExpressionProblem(unsupportedException, columnId, row);
    }
  }

  private final ParseException exception;

  private static String createErrorMessage(ParseException exception) {
    return exception.getMessage();
  }

  public CellParseProblem(ParseException exception, String column, int row) {
    super(createErrorMessage(exception), column, row);
    this.exception = exception;
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

    CellParseProblem that = (CellParseProblem) obj;

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
