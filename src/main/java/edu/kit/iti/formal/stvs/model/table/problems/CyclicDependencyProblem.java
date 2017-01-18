package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.util.List;
import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class CyclicDependencyProblem extends SpecProblem {

  private final int row;
  private final List<SpecIoVariable> cycle;

  public CyclicDependencyProblem(int row, List<SpecIoVariable> cycle) {
    this.row = row;
    this.cycle = cycle;
  }

  @Override
  public <R> R match(
      Function<TypeErrorProblem, R> matchTypeError,
      Function<InvalidIoVarProblem, R> matchInvalidIoVar,
      Function<CyclicDependencyProblem, R> matchCyclicDependency,
      Function<ParseErrorProblem, R> matchParseError,
      Function<DurationProblem, R> matchDurationProblem) {
    return matchCyclicDependency.apply(this);
  }

  @Override
  public String getErrorMessage() {
    return null;
  }

  public int getRow() {
    return row;
  }

  public List<SpecIoVariable> getCycle() {
    return cycle;
  }
}
