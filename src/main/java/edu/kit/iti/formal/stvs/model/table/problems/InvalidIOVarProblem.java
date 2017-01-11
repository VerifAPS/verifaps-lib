package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.SpecIOVariable;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class InvalidIOVarProblem extends SpecProblem {

    public enum Type {
        INVALID_NAME,
        INVALID_TYPE
    }

    private SpecIOVariable column;

    public InvalidIOVarProblem(SpecIOVariable column) {
        this.column = column;
    }

    @Override
    public <R> R match(
            Function<TypeErrorProblem, R> matchTypeError,
            Function<InvalidIOVarProblem, R> matchInvalidIOVar,
            Function<CyclicDependencyProblem, R> matchCyclicDependency,
            Function<ParseErrorProblem, R> matchParseError,
            Function<DurationProblem, R> matchDurationProblem) {
        return matchInvalidIOVar.apply(this);
    }

    @Override
    public String getErrorMessage() {
        return null;
    }

}
