package edu.kit.iti.formal.stvs.model.expressions;

/**
 * runtime-representation for integer values of {@link Expression}s.
 * <p>
 * <p>This is not a singleton (in contrast to {@link ValueBool}), since
 * many different instances can be created at runtime.
 *
 * @author Philipp
 */
public class ValueInt implements Value {

  private final int value;

  /**
   * @param value the integer this value should represent.
   */
  public ValueInt(int value) {
    this.value = value;
  }

  @Override
  public <R> R match(
      ValueIntegerHandler<R> matchInt,
      ValueBooleanHandler<R> matchBoolean,
      ValueEnumHandler<R> matchEnum) {
    return matchInt.handle(value);
  }

  public int getValue() {
    return value;
  }

  public boolean equals(ValueInt other) {
    return other != null && value == other.value;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof ValueInt)) {
      return false;
    }

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

  @Override
  public String getValueString() {
    return Integer.toString(getValue());
  }
}
