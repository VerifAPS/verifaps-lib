package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation for boolean types.
 * This is a singleton since this class does not have any state.
 *
 * @author Philipp
 */
object TypeBool : Type {
    override fun checksAgainst(other: Type): Boolean {
        return other.match({ false }, { true }, { otherEnum: TypeEnum? -> false })!!
    }

    override val typeName: String
        get() = "BOOL"

    override fun parseLiteral(literal: String): Value? {
        if ("true".equals(literal, ignoreCase = true)) {
            return ValueBool.TRUE
        }
        if ("false".equals(literal, ignoreCase = true)) {
            return ValueBool.FALSE
        }
        return null
    }

    override fun generateDefaultValue(): Value {
        return ValueBool.FALSE
    }

    override fun toString(): String {
        return "TypeBool"
    }
}
