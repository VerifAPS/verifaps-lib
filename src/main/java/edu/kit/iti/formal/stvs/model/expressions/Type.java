package edu.kit.iti.formal.stvs.model.expressions;

import java.util.function.Function;
import java.util.function.Supplier;

public interface Type {

    public <R> R match(
            Supplier<R> matchIntType,
            Supplier<R> matchBoolType,
            Function<TypeEnum, R> matchEnumType);

    public boolean checksAgainst(Type other);

    public String getTypeName();
}
