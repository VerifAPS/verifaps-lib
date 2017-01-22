package edu.kit.iti.formal.stvs.model.table.problems;

import java.util.function.Function;

/**
 * @author Benjamin Alt
 */
public class DurationProblem extends SpecProblem {

  private final int row;
  private final String errorMessage;

  public DurationProblem(String errorMessage, int row) {
    this.row = row;
    this.errorMessage = errorMessage;
  }

  @Override
  public <R> R match(
      Function<TypeErrorProblem, R> matchTypeError,
      Function<InvalidIoVarProblem, R> matchInvalidIoVar,
      Function<CyclicDependencyProblem, R> matchCyclicDependency,
      Function<ParseErrorProblem, R> matchParseError,
      Function<DurationProblem, R> matchDurationProblem) {
    return matchDurationProblem.apply(this);
  }

  @Override
  public String getErrorMessage() {
    return errorMessage;
  }

  public int getRow() {
    return row;
  }
}
