package edu.kit.iti.formal.stvs.model.common

/**
 * The category of a variable.
 *
 * @author Philipp
 */
enum class VariableCategory(val defaultRole: VariableRole) {
    INPUT(VariableRole.ASSUME), OUTPUT(VariableRole.ASSERT),
    INOUT(VariableRole.ASSERT), LOCAL(VariableRole.ASSUME)
}