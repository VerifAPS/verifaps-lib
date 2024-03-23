package edu.kit.iti.formal.stvs.model.common;

/**
 * Base class for input/output variables.
 *
 * @author Benjamin Alt
 */
public abstract class IoVariable implements Variable {

  public abstract VariableCategory getCategory();

  public abstract String getName();

  public abstract String getType();

  /**
   * Is this IoVariable equivalent to another variable, in the sense that its name, type and
   * category are identical to those of the other IoVariable? This is not the same as equals(),
   * because it may be desirable that instances of different child classes (e.g. SpecIoVariable
   * and CodeIoVariable) match, but are not equals because they are instances of different classes.
   * @param other The IoVariable to compare this instance to
   * @return True if the IoVariables match, false otherwise
   */
  public boolean matches(IoVariable other) {
    return getName().equals(other.getName()) && getType().equals(other.getType())
        && getCategory() == other.getCategory();
  }

  public String getVarDescriptor() {
    return getCategory() + " " + getName() + " : " + getType();
  }
}
