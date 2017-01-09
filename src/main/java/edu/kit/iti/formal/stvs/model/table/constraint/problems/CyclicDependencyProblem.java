package edu.kit.iti.formal.stvs.model.table.constraint.problems;

import edu.kit.iti.formal.stvs.model.common.IOVariable;

import java.util.List;
import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class CyclicDependencyProblem extends SpecProblem {

    private final int row;
    private final List<IOVariable> cycle;

    public CyclicDependencyProblem(int row, List<IOVariable> cycle) {
        this.row = row;
        this.cycle = cycle;
    }

    @Override
    public <R> R match(
            Function<TypeErrorProblem, R> matchTypeError,
            Function<InvalidIOVarProblem, R> matchInvalidIOVar,
            Function<CyclicDependencyProblem, R> matchCyclicDependency,
            Function<ParseErrorProblem, R> matchParseError) {
        return matchCyclicDependency.apply(this);
    }

    public int getRow() {
        return row;
    }

    public List<IOVariable> getCycle() {
        return cycle;
    }
}
