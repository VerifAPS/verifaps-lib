package edu.kit.iti.formal.stvs.model.expressions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * runtime-representation for enum types.
 * <p>
 * This is (in contrast to {@link TypeInt} or {@link TypeBool}) NOT a singleton, since different
 * instances of this can be created at runtime.
 *
 * @author Philipp
 */
public class TypeEnum implements Type {

  private final String enumTypeName;
  private final Map<String, ValueEnum> valueMap;
  private final List<ValueEnum> valueList;

  /**
   * Create a new enum-type. This should only happen, when an enum is parsed in st-code.
   * <p>
   * St-code example definition of an enum: <tt>COLORS : (red, green, blue)</tt>
   *
   * @param enumTypeName the type name (<tt>COLORS</tt> in this example)
   * @param values the possible values that this enum can be ([<tt>red</tt>, <tt>green</tt>,
   *        <tt>blue</tt>] in this example)
   */
  public TypeEnum(String enumTypeName, List<String> values) {
    this.enumTypeName = enumTypeName;
    this.valueMap = new HashMap<>();
    this.valueList = new ArrayList<>();
    values.forEach((valueName) -> {
      ValueEnum valueEnum = new ValueEnum(valueName, this);
      valueMap.put(valueName, valueEnum);
      valueList.add(valueEnum);
    });
  }

  @Override
  public <R> R match(TypeIntegerHandler<R> matchIntType, TypeBooleanHandler<R> matchBoolType,
      TypeEnumHandler<R> matchEnumType) {
    return matchEnumType.handle(this);
  }

  @Override
  public boolean checksAgainst(Type other) {
    return other.match(() -> false, () -> false,
        (otherEnum) -> otherEnum.getTypeName().equals(getTypeName()));
  }

  @Override
  public String getTypeName() {
    return enumTypeName;
  }

  @Override
  public Optional<Value> parseLiteral(String literal) {
    return Optional.ofNullable(valueMap.get(literal));
  }

  @Override
  public Value generateDefaultValue() {
    // return first element in the values array
    // TODO: Handle Enum without any values?
    // Could such an enum even be represented in ST code?
    return valueMap.values().iterator().next();
  }

  public List<ValueEnum> getValues() {
    return valueList;
  }

  public ValueEnum valueOf(String enumName) {
    ValueEnum enumVal = valueMap.get(enumName);
    if (enumVal == null) {
      throw new RuntimeException("No enum value \"" + enumName + "\" for enum type: " + this);
    } else {
      return enumVal;
    }
  }

  public boolean equals(TypeEnum other) {
    return enumTypeName.equals(other.enumTypeName);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof TypeEnum)) {
      return false;
    }

    TypeEnum typeEnum = (TypeEnum) obj;

    if (!enumTypeName.equals(typeEnum.enumTypeName)) {
      return false;
    }
    return valueMap.keySet().equals(typeEnum.valueMap.keySet());

  }

  @Override
  public int hashCode() {
    int result = enumTypeName.hashCode();
    result = 31 * result + valueMap.keySet().hashCode();
    return result;
  }

  public String toString() {
    return "TypeEnum(" + getTypeName() + " : " + valueMap.keySet() + ")";
  }

}
