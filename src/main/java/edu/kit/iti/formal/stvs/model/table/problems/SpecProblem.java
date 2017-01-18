package edu.kit.iti.formal.stvs.model.table.problems;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
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
