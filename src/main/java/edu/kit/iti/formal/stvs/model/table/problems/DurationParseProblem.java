package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;

/**
 * <p>The model for a {@link ParseException} in duration cells.
 * (Generated when a duration cell expression is <tt>[1,</tt> or <tt>[a,b]</tt>, etc.)</p>
 *
 * @author Benjamin Alt
 */
public class DurationParseProblem extends DurationProblem {

  /**
   * <p>Tries to parse a duration into it's formal model {@link LowerBoundedInterval}.</p>
   *
   * <p>If that fails, it throws a {@link DurationParseProblem}</p>
   * @param row the row of the duration to be parsed
   * @param duration the duration cell to be parsed
   * @return the formal model of a duration cell, if successfully parsed
   * @throws DurationParseProblem the parse problem if the duration could not be parsed
   */
  public static LowerBoundedInterval tryParseDuration(int row, ConstraintDuration duration)
      throws DurationParseProblem {
    try {
      return IntervalParser.parse(duration.getAsString());
    } catch (ParseException parseException) {
      throw new DurationParseProblem(parseException, row);
    }
  }

  private static String createErrorMessage(ParseException exception) {
    return exception.getMessage();
  }

  /**
   * <p>Constructor for a Parse Problem for a given {@link ParseException}.</p>
   *
   * <p>Creates a better GUI message from the given exception.</p>
   *
   * @param exception the exception that occurred when parsing the duration cell
   * @param row the row of the duration cell that produced the given exception
   */
  public DurationParseProblem(ParseException exception, int row) {
    super(createErrorMessage(exception), row);
  }
}
