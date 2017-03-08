package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

/**
 * A valid I/O variable. This variable may appear in a {@link ValidSpecification}. Their names
 * have been checked (conform to valid identifier pattern) and their types are parsed
 * {@link Type} objects. For the validation logic, see
 * {@link edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator}.
 *
 * @author Philipp
 */
public class ValidIoVariable extends IoVariable {

  private final VariableCategory category;
  private final String name;
  private final Type type;

  /**
   * Create a new ValidIoVariable with a given category, name and type.
   * @param category The category of this variable
   * @param name The name of this variable
   * @param type The type of this variable
   */
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

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    ValidIoVariable that = (ValidIoVariable) obj;

    if (getCategory() != that.getCategory()) {
      return false;
    }
    if (getName() != null ? !getName().equals(that.getName()) : that.getName() != null) {
      return false;
    }
    return getType() != null ? getType().equals(that.getType()) : that.getType() == null;
  }

  @Override
  public int hashCode() {
    int result = getCategory() != null ? getCategory().hashCode() : 0;
    result = 31 * result + (getName() != null ? getName().hashCode() : 0);
    result = 31 * result + (getType() != null ? getType().hashCode() : 0);
    return result;
  }
}
