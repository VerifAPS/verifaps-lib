package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;

/**
 * @author Benjamin Alt
 */
public class DurationParseProblem extends DurationProblem {

  private static String createErrorMessage(ParseException exception) {
    return exception.getMessage();
  }

  public DurationParseProblem(ParseException exception, int row) {
    super(createErrorMessage(exception), row);
  }


}
