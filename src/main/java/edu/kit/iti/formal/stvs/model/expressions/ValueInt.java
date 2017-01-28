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

  public int getValue() {
    return value;
  }

  public boolean equals(ValueInt other) {
    return other != null && value == other.value;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof ValueInt)) return false;

    ValueInt valueInt = (ValueInt) obj;

    return value == valueInt.value;

  }

  @Override
  public int hashCode() {
    return value;
  }

  public String toString() {
    return "ValueInt(" + value + ")";
  }

  @Override
  public Type getType() {
    return TypeInt.INT;
  }
}
