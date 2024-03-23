package edu.kit.iti.formal.stvs.model.common;

/**
 * The category of a variable.
 *
 * @author Philipp
 */
public enum VariableCategory {
  INPUT(VariableRole.ASSUME), OUTPUT(VariableRole.ASSERT),
  INOUT(VariableRole.ASSERT), LOCAL(VariableRole.ASSUME);

  private final VariableRole defaultRole;

  VariableCategory(VariableRole defaultRole) {
    this.defaultRole = defaultRole;
  }

  public VariableRole getDefaultRole() {
    return defaultRole;
  }
}