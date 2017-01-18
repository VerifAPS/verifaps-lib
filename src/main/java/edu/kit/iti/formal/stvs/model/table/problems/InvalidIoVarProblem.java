package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class InvalidIoVarProblem extends SpecProblem {

  public enum Type {
    INVALID_NAME,
    INVALID_TYPE
  }

  private SpecIoVariable column;

  public InvalidIoVarProblem(SpecIoVariable column) {
    this.column = column;
  }

  @Override
  public <R> R match(
      Function<TypeErrorProblem, R> matchTypeError,
      Function<InvalidIoVarProblem, R> matchInvalidIoVar,
      Function<CyclicDependencyProblem, R> matchCyclicDependency,
      Function<ParseErrorProblem, R> matchParseError,
      Function<DurationProblem, R> matchDurationProblem) {
    return matchInvalidIoVar.apply(this);
  }

  @Override
  public String getErrorMessage() {
    return null;
  }

}
