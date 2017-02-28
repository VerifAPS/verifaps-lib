package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by philipp on 09.02.17.
 *
 * @author Philipp
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
