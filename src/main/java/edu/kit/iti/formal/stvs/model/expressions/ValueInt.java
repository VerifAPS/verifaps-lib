package edu.kit.iti.formal.stvs.model.expressions;

import java.util.function.Function;
import java.util.function.IntFunction;

public class ValueInt implements Value {

	private final int value;
	
	public ValueInt(int value) {
		this.value = value;
	}

	@Override
	public <R> R match(
			IntFunction<R> matchInt, 
			Function<Boolean, R> matchBoolean, 
			Function<ValueEnum, R> matchEnum) {
		return matchInt.apply(value);
	}
	
	public String toString() {
		return "IntValue(" + value + ")";
	}

	@Override
	public Type getType() {
		return TypeFactory.INT;
	}

}
