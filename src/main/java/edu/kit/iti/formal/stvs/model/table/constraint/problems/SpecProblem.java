package edu.kit.iti.formal.stvs.model.table.constraint.problems;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public abstract class SpecProblem {

    public abstract <R> R match(
            Function<TypeErrorProblem, R> matchTypeError,
            Function<InvalidIOVarProblem, R> matchInvalidIOVar,
            Function<CyclicDependencyProblem, R> matchCyclicDependency,
            Function<ParseErrorProblem, R> matchParseError
    );
}
