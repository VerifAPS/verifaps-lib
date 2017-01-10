package edu.kit.iti.formal.stvs.model.table.constraint.problems;

import edu.kit.iti.formal.stvs.model.common.IOVariable;

import java.util.function.Function;

/**
 * Created by philipp on 09.01.17.
 */
public class InvalidIOVarProblem extends SpecProblem {

    public enum Type {
        INVALID_NAME,
        INVALID_TYPE
    }

    private final IOVariable column;
    private final Type type;

    public InvalidIOVarProblem(IOVariable column, Type type) {
        this.column = column;
        this.type = type;
    }

    @Override
    public <R> R match(
            Function<TypeErrorProblem, R> matchTypeError,
            Function<InvalidIOVarProblem, R> matchInvalidIOVar,
            Function<CyclicDependencyProblem, R> matchCyclicDependency,
            Function<ParseErrorProblem, R> matchParseError) {
        return matchInvalidIOVar.apply(this);
    }

    public IOVariable getIOVariable() {
        return column;
    }

    public Type getType() {
        return type;
    }

}
