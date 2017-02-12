package edu.kit.iti.formal.stvs.model.common;

/**
 * Created by philipp on 09.01.17.
 */
public class CodeIoVariable extends IoVariable {

  private final VariableCategory category;
  private final String type;
  private final String name;

  /**
   * Creates a variable that appears in the code.
   * @param category The category of the variable
   * @param type     The identifier of the type of the variable
   * @param name     The name of the Variable
   */
  public CodeIoVariable(VariableCategory category, String type, String name) {
    if (category == null || type == null || name == null) {
      throw new NullPointerException();
    }
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
  public String getType() {
    return type;
  }

  public boolean equals(CodeIoVariable other) {
    return type.equals(other.type) && name.equals(other.name) && category.equals(other.category);
  }

  @Override
  public boolean equals(Object o) {
    if (o == null) return false;
    if (!(o instanceof CodeIoVariable)) return false;
    CodeIoVariable other = (CodeIoVariable) o;
    return equals(other);
  }

  public String toString() {
    return "CodeIoVariable(" + category + " " + name + " : " + type + ")";
  }
}
