package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class TypeErrorProblem extends SpecProblem {

    private final SpecIoVariable column;
    private final int row;
    private final TypeCheckException typeCheckException;

    public TypeErrorProblem(SpecIoVariable column, int row, TypeCheckException typeCheckException) {
        this.column = column;
        this.row = row;
        this.typeCheckException = typeCheckException;
    }

    @Override
    public <R> R match(
            Function<TypeErrorProblem, R> matchTypeError,
            Function<InvalidIOVarProblem, R> matchInvalidIOVar,
            Function<CyclicDependencyProblem, R> matchCyclicDependency,
            Function<ParseErrorProblem, R> matchParseError,
            Function<DurationProblem, R> matchDurationProblem) {
        return matchTypeError.apply(this);
    }

    public TypeCheckException getTypeCheckException() {
        return null;
    }

    @Override
    public String getErrorMessage() {
        return null;
    }

    public SpecIoVariable getIOVariable() {
        return column;
    }

    public int getRow() {
        return row;
    }
}
