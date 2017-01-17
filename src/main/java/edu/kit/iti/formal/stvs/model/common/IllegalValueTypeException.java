package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;

/**
 * Defines an Exception that should be thrown if a {@link Value} has a different {@link Value} than expected.
 */
public class IllegalValueTypeException extends Exception {
  private static final long serialVersionUID = 2L;

  private final Value mistypedValue;
  private final Type expectedType;

  /**
   * Creates the exception
   *
   * @param mistypedValue Value with mismatched type
   * @param expectedType Type that the Value was expected to be
   * @param message Additional message
   */
  public IllegalValueTypeException(Value mistypedValue, Type expectedType, String message) {
    super(message + "\nGiven Type: " + mistypedValue.getType().getTypeName()
            + "\nExpected Type: " + expectedType.getTypeName());
    this.mistypedValue = mistypedValue;
    this.expectedType = expectedType;
  }

  public Value getMistypedValue() {
    return mistypedValue;
  }

  public Type getExpectedType() {
    return expectedType;
  }
}
