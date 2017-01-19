package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by philipp on 09.01.17.
 */
public class CodeIoVariable extends IoVariable {

  private final VariableCategory category;
  private final Type type;
  private final String name;

  /**
   * Creates a variable that appears in the code.
   *
   * @param category The category of the variable
   * @param type     The type of the variable
   * @param name     The name of the Variable
   */
  public CodeIoVariable(VariableCategory category, Type type, String name) {
    this.category = category;
    this.type = type;
    this.name = name;
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
