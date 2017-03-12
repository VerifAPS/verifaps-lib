package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;

/**
 * A valid free variable. Its name is a valid identifier, its type is a parsed {@link Type}
 * object (instead of Strings denoting only the type name) and its value is a parsed
 * {@link Value} object of the respective type.
 *
 * @author Philipp
 */
public class ValidFreeVariable {

  private final String name;
  private final Type type;
  private final Value defaultValue;

  /**
   * Create a new ValidFreeVariable with a given name, type and default value.
   * @param name The name of this FreeVariable
   * @param type The type of this FreeVariable
   * @param defaultValue The default value of this FreeVariable
   */
  public ValidFreeVariable(String name, Type type, Value defaultValue) {
    this.name = name;
    this.type = type;
    this.defaultValue = defaultValue;
  }

  public String getName() {
    return name;
  }

  public Type getType() {
    return type;
  }

  public Value getDefaultValue() {
    return defaultValue;
  }
}
