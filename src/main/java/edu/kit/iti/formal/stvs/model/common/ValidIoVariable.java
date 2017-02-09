package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by philipp on 09.02.17.
 */
public class ValidIoVariable extends IoVariable {

  private final VariableCategory category;
  private final String name;
  private final Type type;

  public ValidIoVariable(VariableCategory category, String name, Type type) {
    this.category = category;
    this.name = name;
    this.type = type;
  }

  public VariableCategory getCategory() {
    return category;
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public String getType() {
    return getValidType().getTypeName();
  }

  public Type getValidType() {
    return type;
  }

}
