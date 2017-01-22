package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.util.function.Function;

/**
 * @author Benjamin Alt
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
      Function<InvalidIoVarProblem, R> matchInvalidIoVar,
      Function<CyclicDependencyProblem, R> matchCyclicDependency,
      Function<ParseErrorProblem, R> matchParseError,
      Function<DurationProblem, R> matchDurationProblem) {
    return matchParseError.apply(this);
  }

  @Override
  public String getErrorMessage() {
    return errorMessage;
  }

  public SpecIoVariable getIoVariable() {
    return ioVariable;
  }

  public int getRow() {
    return row;
  }
}
