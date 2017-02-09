package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;

/**
 * Created by philipp on 09.02.17.
 */
public class ValidFreeVariable {

  private final String name;
  private final Type type;
  private final Value defaultValue;

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
