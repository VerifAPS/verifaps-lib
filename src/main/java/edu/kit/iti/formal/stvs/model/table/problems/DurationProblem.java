package edu.kit.iti.formal.stvs.model.table.problems;

import java.util.function.Function;

/**
 * Created by Philipp on 10.01.2017.
 */
public class DurationProblem extends SpecProblem {

  private final int row;
  private final String errorMessage;

  public DurationProblem(int row, String errorMessage) {
    this.row = row;
    this.errorMessage = errorMessage;
  }

  @Override
  public <R> R match(
      Function<TypeErrorProblem, R> matchTypeError,
      Function<InvalidIOVarProblem, R> matchInvalidIOVar,
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
