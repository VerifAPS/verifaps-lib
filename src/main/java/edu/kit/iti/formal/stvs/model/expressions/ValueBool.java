package edu.kit.iti.formal.stvs.model.expressions;

/**
 * runtime-representation for boolean values of {@link Expression}s.
 * <p>
 * This is a singleton with two instances, TRUE and FALSE, since there
 * is no state to the values.
 *
 * @author Philipp
 */
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
      ValueIntegerHandler<R> matchInt,
      ValueBooleanHandler<R> matchBoolean,
      ValueEnumHandler<R> matchEnum) {
    return matchBoolean.handle(value);
  }

  public boolean getValue() {
    return value;
  }

  @Override
  public Type getType() {
    return TypeBool.BOOL;
  }

  @Override
  public String getValueString() {
    if (getValue()) {
      return "TRUE";
    } else {
      return "FALSE";
    }
  }

  public String toString() {
    return "ValueBool(" + value + ")";
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof ValueBool)) {
      return false;
    }

    ValueBool valueBool = (ValueBool) obj;

    return value == valueBool.value;

  }

  @Override
  public int hashCode() {
    return (value ? 1 : 0);
  }
}
