package edu.kit.iti.formal.stvs.model.expressions;

import java.util.function.Function;
import java.util.function.IntFunction;

public interface Value {
	
	public <R> R match(
			IntFunction<R> matchInt,
			Function<Boolean,R> matchBoolean,
			Function<ValueEnum,R> matchEnum
			);
	
	public Type getType();

}
