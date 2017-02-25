package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Optional;

/**
 * The super-interface for all Types.
 * @author Philipp
 */
public interface Type {

  /**
   * matches the actual type present. Subclasses call the correct function.
   * @param matchIntType in case its a {@link TypeInt}
   * @param matchBoolType in case its a {@link TypeBool}
   * @param matchEnumType in case its a {@link TypeEnum}
   * @param <R> the return type of the visitor
   * @return the return value of the visitor
   */
  <R> R match(
      TypeIntegerHandler<R> matchIntType,
      TypeBooleanHandler<R> matchBoolType,
      TypeEnumHandler<R> matchEnumType);

  /**
   * Finds out whether this type checks against another type, which means
   * any value of this type can be used as a value of the other type.
   *
   * This mostly means type equality or a supertype relation.
   * @param other the other type ot subsume.
   * @return whether it does subsume the other type or not.
   */
  boolean checksAgainst(Type other);

  /**
   * Get the type name of this type in a human-readable format
   * (in contrast to this classes' toString()).
   * This can be used to show the type in a GUI, for example.
   * @return a string that should match the type name as it is
   *         usually used in st-code.
   */
  String getTypeName();

  /**
   * Parse a literal of this type to a value. Can
   * be used for parsing user-input into TextFields when
   * the type is known, for example.
   * @param literal the literal string to parse
   * @return optionally a resulting value
   */
  Optional<Value> parseLiteral(String literal);

  /**
   * For any <tt>{@link Type} type</tt> the following must be true:
   * <tt>type.generateDefaultValue().getErrorType().checksAgainst(type)</tt>
   * @return a default value of this given type.
   */
  Value generateDefaultValue();
}
