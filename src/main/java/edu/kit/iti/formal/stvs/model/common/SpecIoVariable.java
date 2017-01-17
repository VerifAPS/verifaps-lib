package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by csicar on 11.01.17.
 */
public class SpecIoVariable extends IoVariable {
  private String name;
  private Type type;
  private VariableCategory category;

  /**
   * Creates a variable that appears in the specification.
   *
   * @param category The category of the variable
   * @param type     The type of the variable
   * @param name     The name of the Variable
   */
  public SpecIoVariable(VariableCategory category, Type type, String name) {
    this.category = category;
    this.type = type;
    this.name = name;
  }

  public void setCategory(VariableCategory category) {
    this.category = category;
  }

  public void setName(String name) {
    this.name = name;
  }

  public void setType(Type type) {
    this.type = type;
  }

  @Override
  public VariableCategory getCategory() {
    return category;
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public Type getType() {
    return type;
  }
}
