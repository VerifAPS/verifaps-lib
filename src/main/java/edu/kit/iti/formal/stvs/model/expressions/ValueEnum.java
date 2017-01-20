package edu.kit.iti.formal.stvs.model.expressions;

import java.util.function.Function;
import java.util.function.IntFunction;

public class ValueEnum implements Value {

  private final String enumValue;
  private final TypeEnum enumType;

  public ValueEnum(String enumValue, TypeEnum enumType) {
    this.enumValue = enumValue;
    this.enumType = enumType;
  }

  @Override
  public <R> R match(
      IntFunction<R> matchInt,
      Function<Boolean, R> matchBoolean,
      Function<ValueEnum, R> matchEnum) {
    return null;
  }

  public boolean equals(ValueEnum other) {
    return other != null && enumValue.equals(other.enumValue) && enumType.equals(other.enumType);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof ValueEnum)) return false;

    ValueEnum valueEnum = (ValueEnum) obj;

    if (!enumValue.equals(valueEnum.enumValue)) return false;
    return enumType.equals(valueEnum.enumType);

  }

  @Override
  public int hashCode() {
    int result = enumValue.hashCode();
    result = 31 * result + enumType.hashCode();
    return result;
  }

  @Override
  public Type getType() {
    return enumType;
  }

  public String getEnumValue() {
    return enumValue;
  }

  public String toString() {
    return "ValueEnum(" + enumValue + ")";
  }

}
