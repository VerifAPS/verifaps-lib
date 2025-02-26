package edu.kit.iti.formal.stvs.model.common

import edu.kit.iti.formal.stvs.model.expressions.Expression
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.Value

/**
 * A valid free variable. Its name is a valid identifier, its type is a parsed [Type]
 * object (instead of Strings denoting only the type name) and its value is a parsed
 * [Value] object of the respective type.
 *
 *
 * Create a new ValidFreeVariable with a given name, type and default value.
 * @param name The name of this FreeVariable
 * @param type The type of this FreeVariable
 * @param constraint constraint expression for this global variable
 *
 * @author Philipp
 */
data class ValidFreeVariable(val name: String, val type: Type, val constraint: Expression?) {
    fun asIOVariable(): ValidIoVariable {
        return ValidIoVariable(VariableCategory.INPUT, name, type, VariableRole.ASSUME)
    }
}
