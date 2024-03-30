package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation for int types.
 * This class is a singleton, since it does not hold any state at all.
 *
 * @author Philipp
 */
class TypeInt private constructor() : Type {
    override fun <R> match(
        matchIntType: TypeIntegerHandler<R>, matchBoolType: TypeBooleanHandler<R>,
        matchEnumType: TypeEnumHandler<R>
    ): R? {
        return matchIntType.handle()
    }

    override fun checksAgainst(other: Type): Boolean {
        return other.match({ true }, { false }, { otherEnum: TypeEnum? -> false })!!
    }

    override val typeName: String
        get() = "INT"

    override fun parseLiteral(literal: String) = literal.toIntOrNull()?.let { ValueInt(it) }

    override fun generateDefaultValue(): Value {
        return ValueInt(1)
    }

    override fun toString(): String {
        return "TypeInt"
    }

    override fun equals(obj: Any?): Boolean {
        return obj is TypeInt
    }

    companion object {
        @JvmField
        val INT: TypeInt = TypeInt()
    }
}
