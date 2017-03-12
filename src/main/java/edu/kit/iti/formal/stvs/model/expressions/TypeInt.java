package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Optional;

/**
 * Runtime-representation for int types.
 * This class is a singleton, since it does not hold any state at all.
 *
 * @author Philipp
 */
public class TypeInt implements Type {

  public static final TypeInt INT = new TypeInt();

  private TypeInt() {}

  @Override
  public <R> R match(TypeIntegerHandler<R> matchIntType, TypeBooleanHandler<R> matchBoolType,
      TypeEnumHandler<R> matchEnumType) {
    return matchIntType.handle();
  }

  @Override
  public boolean checksAgainst(Type other) {
    return other.match(() -> true, () -> false, (otherEnum) -> false);
  }

  @Override
  public String getTypeName() {
    return "INT";
  }

  @Override
  public Optional<Value> parseLiteral(String literal) {
    try {
      return Optional.of(new ValueInt(Integer.parseInt(literal)));
    } catch (NumberFormatException e) {
      return Optional.empty();
    }
  }

  @Override
  public Value generateDefaultValue() {
    return new ValueInt(1);
  }

  public String toString() {
    return "TypeInt";
  }

  @Override
  public boolean equals(Object obj) {
    return obj instanceof TypeInt;
  }
}
