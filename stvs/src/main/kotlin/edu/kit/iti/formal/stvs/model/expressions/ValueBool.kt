package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation for boolean values of [Expression]s.
 * This is a singleton with two instances, TRUE and FALSE, since there is no state to the values.
 *
 * @author Philipp
 */
class ValueBool private constructor(val value: Boolean) : Value {
    override fun <R> match(
        matchInt: ValueIntegerHandler<R>, matchBoolean: ValueBooleanHandler<R>,
        matchEnum: ValueEnumHandler<R>
    ): R? {
        return matchBoolean.handle(value)
    }

    override val type: Type
        get() = TypeBool.Companion.BOOL

    override val valueString: String
        get() = if (value) {
            "TRUE"
        } else {
            "FALSE"
        }

    override fun toString(): String {
        return "ValueBool($value)"
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj !is ValueBool) {
            return false
        }

        return value == obj.value
    }

    override fun hashCode(): Int {
        return (if (value) 1 else 0)
    }

    companion object {
        @JvmField
        val TRUE: ValueBool = ValueBool(true)
        @JvmField
        val FALSE: ValueBool = ValueBool(false)

        @JvmStatic
        fun of(bool: Boolean): ValueBool {
            return if (bool) TRUE else FALSE
        }
    }
}
