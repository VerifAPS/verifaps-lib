package edu.kit.iti.formal.stvs.model.expressions;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;

public class TypeEnum implements Type {

  private final String enumTypeName;
  private final Map<String, ValueEnum> valueMap;

  public TypeEnum(String enumTypeName, List<String> values) {
    this.enumTypeName = enumTypeName;
    this.valueMap = new HashMap<>();
    values.forEach((valueName) -> {
      valueMap.put(valueName, new ValueEnum(valueName, this));
    });
  }

  @Override
  public <R> R match(
      Supplier<R> matchIntType,
      Supplier<R> matchBoolType,
      Function<TypeEnum, R> matchEnumType) {
    return matchEnumType.apply(this);
  }

  @Override
  public boolean checksAgainst(Type other) {
    return other.match(
        () -> false,
        () -> false,
        (otherEnum) -> otherEnum.getTypeName().equals(getTypeName())
    );
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

  // The fuck is this? TODO: Maybe remove this method
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
    if (this == obj) return true;
    if (!(obj instanceof TypeEnum)) return false;

    TypeEnum typeEnum = (TypeEnum) obj;

    if (!enumTypeName.equals(typeEnum.enumTypeName)) return false;
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
