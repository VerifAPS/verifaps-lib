package edu.kit.iti.formal.stvs.model.table.problems;

import java.util.function.Function;

/**
 * @author Benjamin Alt
 */
public abstract class SpecProblem {


  public abstract <R> R match(
      Function<TypeErrorProblem, R> matchTypeError,
      Function<InvalidIoVarProblem, R> matchInvalidIoVar,
      Function<CyclicDependencyProblem, R> matchCyclicDependency,
      Function<ParseErrorProblem, R> matchParseError,
      Function<DurationProblem, R> matchDurationProblem);

  public abstract String getErrorMessage();
}
