package edu.kit.iti.formal.stvs.model.expressions;

/**
 * The common interface for values of Expressions. Values are visitable and have a type.
 *
 * @author Philipp
 */
public interface Value {

  /**
   * Visitor function for Values. Subclasses call the respective Functions.
   *
   * @param matchInt a function for handling an integer value
   * @param matchBoolean a function for handling a boolean value
   * @param matchEnum a function for handling an enum value
   * @param <R> the return type of the visitor functions
   * @return the return value of the visitor function called
   */
  <R> R match(ValueIntegerHandler<R> matchInt, ValueBooleanHandler<R> matchBoolean,
      ValueEnumHandler<R> matchEnum);

  /**
   * Should return type of this value.
   * @return the type for this expression. (returns a TypeBool for a ValueInt for example)
   */
  Type getType();

  /**
   * Should return a string representation of this value.
   * @return a String representation of the represented value
   */
  String getValueString();
}
