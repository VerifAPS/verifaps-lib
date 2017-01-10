package edu.kit.iti.formal.stvs.model.table.constraint.problems;

import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class ParseErrorProblem extends SpecProblem {

    // TODO: Give Parse Error information
    private final VariableIdentifier column;
    private final int row;

    public ParseErrorProblem(VariableIdentifier column, int row) {
        this.column = column;
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

    public VariableIdentifier getColumn() {
        return column;
    }

    public int getRow() {
        return row;
    }
}
