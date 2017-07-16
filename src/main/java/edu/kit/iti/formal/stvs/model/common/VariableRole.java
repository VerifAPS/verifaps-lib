package edu.kit.iti.formal.stvs.model.common;

/**
 * Created by csicar on 06.07.17.
 * specifies what role (can be assume or assert) a variable should be used as in Verification and
 * Concretization
 * ASSUME can be used for VariableCategories INPUT, INOUT, LOCAL
 * ASSERT can be used for VariableCategories OUTPUT, INOUT, LOCAl
 */
public enum VariableRole {
  ASSUME, ASSERT
}
