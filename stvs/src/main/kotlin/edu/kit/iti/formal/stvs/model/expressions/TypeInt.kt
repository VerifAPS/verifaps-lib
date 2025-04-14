package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation for int types.
 * This class is a singleton, since it does not hold any state at all.
 *
 * @author Philipp
 */
object TypeInt : Type {
    override fun checksAgainst(other: Type): Boolean =
        other.match({ true }, { false }, { otherEnum: TypeEnum? -> false })

    override val typeName: String = "INT"

    override fun parseLiteral(literal: String) = literal.toIntOrNull()?.let { ValueInt(it) }

    override fun generateDefaultValue(): Value = ValueInt(1)

    override fun toString(): String = "TypeInt"
}
