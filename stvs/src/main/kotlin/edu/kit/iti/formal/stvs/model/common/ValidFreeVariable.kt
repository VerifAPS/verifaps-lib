package edu.kit.iti.formal.stvs.model.common

import edu.kit.iti.formal.stvs.logic.specification.smtlib.SAtom
import edu.kit.iti.formal.stvs.model.expressions.*

/**
 * A valid free variable. Its name is a valid identifier, its type is a parsed [Type]
 * object (instead of Strings denoting only the type name) and its value is a parsed
 * [Value] object of the respective type.
 *
 * @author Philipp
 */
class ValidFreeVariable
/**
 * Create a new ValidFreeVariable with a given name, type and default value.
 * @param name The name of this FreeVariable
 * @param type The type of this FreeVariable
 * @param defaultValue The default value of this FreeVariable
 */(@JvmField val name: String, @JvmField val type: Type, val constraint: Expression?) {
    fun asIOVariable(): ValidIoVariable {
        return ValidIoVariable(VariableCategory.INPUT, name, type)
    }

    val sMTName: SAtom
        get() = SAtom(String.format("|%s|", name))
}
