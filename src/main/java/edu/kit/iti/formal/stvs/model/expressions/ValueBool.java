package edu.kit.iti.formal.stvs.model.expressions;

import java.util.function.Function;
import java.util.function.IntFunction;

public class ValueBool implements Value {

    private final boolean value;

    public ValueBool(boolean value) {
        this.value = value;
    }

    @Override
    public <R> R match(
            IntFunction<R> matchInt,
            Function<Boolean, R> matchBoolean,
            Function<ValueEnum, R> matchEnum) {
        return matchBoolean.apply(value);
    }

    @Override
    public Type getType() {
        return TypeFactory.BOOL;
    }

}
