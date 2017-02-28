package edu.kit.iti.formal.stvs.model.expressions;

/**
 * runtime-representation for enum values of {@link Expression}s.
 * <p>
 * <p>In contrast to {@link ValueBool} this is not a singleton, since
 * many different instances can be created at runtime.
 * getErrorType of this value always returns a {@link TypeEnum}.
 *
 * @author Philipp
 */
public class ValueEnum implements Value {

  private final String enumValue;
  private final TypeEnum enumType;

  /**
   * package-local. Generate values from TypeEnum!
   * Construct a new value of given type with given constructor.
   *
   * @param enumValue enum constructor (for example <tt>red</tt>)
   * @param enumType  enum type (for example <tt>TypeEnum(COLORS, [red, green, blue])</tt>)
   */
  ValueEnum(String enumValue, TypeEnum enumType) {
    this.enumValue = enumValue;
    this.enumType = enumType;
  }

  @Override
  public <R> R match(
      ValueIntegerHandler<R> matchInt,
      ValueBooleanHandler<R> matchBoolean,
      ValueEnumHandler<R> matchEnum) {
    return matchEnum.handle(this);
  }

  public boolean equals(ValueEnum other) {
    return other != null && enumValue.equals(other.enumValue) && enumType.equals(other.enumType);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof ValueEnum)) {
      return false;
    }

    ValueEnum valueEnum = (ValueEnum) obj;

    if (!enumValue.equals(valueEnum.enumValue)) {
      return false;
    }
    return enumType.equals(valueEnum.enumType);

  }

  @Override
  public int hashCode() {
    int result = enumValue.hashCode();
    result = 31 * result + enumType.hashCode();
    return result;
  }

  @Override
  public TypeEnum getType() {
    return enumType;
  }

  @Override
  public String getValueString() {
    return enumValue;
  }

  public String getEnumValue() {
    return enumValue;
  }

  public String toString() {
    return "ValueEnum(" + enumValue + ")";
  }

}
