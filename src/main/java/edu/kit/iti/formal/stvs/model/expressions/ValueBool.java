package edu.kit.iti.formal.stvs.model.expressions;

import java.util.function.Function;
import java.util.function.IntFunction;

public class ValueBool implements Value {

  public static final ValueBool TRUE = new ValueBool(true);
  public static final ValueBool FALSE = new ValueBool(false);

  public static ValueBool of(boolean bool) {
    return bool ? TRUE : FALSE;
  }

  private final boolean value;

  private ValueBool(boolean value) {
    this.value = value;
  }

  @Override
  public <R> R match(
      IntFunction<R> matchInt,
      Function<Boolean, R> matchBoolean,
      Function<ValueEnum, R> matchEnum) {
    return matchBoolean.apply(value);
  }

  public boolean getValue() {
    return value;
  }

  @Override
  public Type getType() {
    return TypeBool.BOOL;
  }

  public String toString() {
    return "ValueBool(" + value + ")";
  }

}
