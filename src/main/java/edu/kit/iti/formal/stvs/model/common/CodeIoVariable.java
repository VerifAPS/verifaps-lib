package edu.kit.iti.formal.stvs.model.common;

/**
 * An input or output variable declared in the code.
 *
 * @author Philipp
 */
public class CodeIoVariable extends IoVariable {

  private final VariableCategory category;
  private final String type;
  private final String name;

  /**
   * Creates a variable that appears in the code.
   *
   * @param category The category of the variable
   * @param type The identifier of the type of the variable
   * @param name The name of the Variable
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

  private boolean equals(CodeIoVariable other) {
    if (other == null) {
      return false;
    }
    return type.equals(other.type) && name.equals(other.name) && category.equals(other.category);
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    }
    if (!(obj instanceof CodeIoVariable)) {
      return false;
    }
    CodeIoVariable other = (CodeIoVariable) obj;
    return equals(other);
  }

  @Override
  public String toString() {
    return "CodeIoVariable(" + category + " " + name + " : " + type + ")";
  }
}
