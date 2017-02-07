package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by csicar on 11.01.17.
 */
public abstract class IoVariable implements Variable {


  public abstract VariableCategory getCategory();

  public abstract String getName();

  public abstract Type getType();

  public boolean matches(IoVariable other) {
    return getName().equals(other.getName())
        && getType().checksAgainst(other.getType())
        && getCategory() == other.getCategory();
  }

  public String getVarDescriptor() {
    return getCategory() + " " + getName() + " : " + getType().getTypeName();
  }
}
