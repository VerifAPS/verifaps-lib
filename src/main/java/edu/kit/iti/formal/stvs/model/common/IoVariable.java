package edu.kit.iti.formal.stvs.model.common;

/**
 * Created by csicar on 11.01.17.
 */
public abstract class IoVariable implements Variable {


  public abstract VariableCategory getCategory();

  public abstract String getName();

  public abstract String getType();

  public boolean matches(IoVariable other) {
    return getName().equals(other.getName())
        && getType().equals(other.getType())
        && getCategory() == other.getCategory();
  }

  public String getVarDescriptor() {
    return getCategory() + " " + getName() + " : " + getType();
  }
}
