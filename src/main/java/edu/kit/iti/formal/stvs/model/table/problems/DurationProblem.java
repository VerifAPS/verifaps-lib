package edu.kit.iti.formal.stvs.model.table.problems;

import java.util.function.Function;

/**
 * Created by Philipp on 10.01.2017.
 */
public class DurationProblem extends SpecProblem {

    // TODO: Give Parse Error information
    private final int row;

    public DurationProblem(int row) {
        this.row = row;
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

    public int getRow() {
        return row;
    }
}
