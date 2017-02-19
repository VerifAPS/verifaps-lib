package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * runtime-representation for boolean types.
 *
 * This is a singleton since this class does not have any state.
 * @author Philipp
 */
public class TypeBool implements Type {

  public static final TypeBool BOOL = new TypeBool();

  private TypeBool() {
  }

  @Override
  public <R> R match(
      Supplier<R> matchIntType,
      Supplier<R> matchBoolType,
      Function<TypeEnum, R> matchEnumType) {
    return matchBoolType.get();
  }

  @Override
  public boolean checksAgainst(Type other) {
    return other.match(
        () -> false,
        () -> true,
        (otherEnum) -> false);
  }

  @Override
  public String getTypeName() {
    return "BOOL";
  }

  @Override
  public Optional<Value> parseLiteral(String literal) {
    if ("true".equalsIgnoreCase(literal)) return Optional.of(ValueBool.TRUE);
    if ("false".equalsIgnoreCase(literal)) return Optional.of(ValueBool.FALSE);
    return Optional.empty();
  }

  @Override
  public Value generateDefaultValue() {
    return ValueBool.FALSE;
  }

  public String toString() {
    return "TypeBool";
  }

  @Override
  public boolean equals(Object obj) {
    return obj instanceof TypeBool;
  }
}
