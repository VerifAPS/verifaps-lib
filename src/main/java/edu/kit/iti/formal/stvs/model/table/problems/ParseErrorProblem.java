package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class ParseErrorProblem extends SpecProblem {

  private final String errorMessage;
  private final SpecIoVariable ioVariable;
  private final int row;

  public ParseErrorProblem(String errorMessage, SpecIoVariable column, int row) {
    this.errorMessage = errorMessage;
    this.ioVariable = column;
    this.row = row;
  }


  @Override
  public <R> R match(
      Function<TypeErrorProblem, R> matchTypeError,
      Function<InvalidIOVarProblem, R> matchInvalidIOVar,
      Function<CyclicDependencyProblem, R> matchCyclicDependency,
      Function<ParseErrorProblem, R> matchParseError,
      Function<DurationProblem, R> matchDurationProblem) {
    return matchParseError.apply(this);
  }

  @Override
  public String getErrorMessage() {
    return null;
  }

  public SpecIoVariable getIOVariable() {
    return ioVariable;
  }

  public int getRow() {
    return row;
  }
}
