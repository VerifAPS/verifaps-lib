package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation for integer values of [Expression]s.
 * This is not a singleton (in contrast to [ValueBool]), since many different instances can be
 * created at runtime.
 *
 * @author Philipp
 */
class ValueInt
/**
 * @param value the integer this value should represent.
 */(val value: Int) : Value {
    override fun <R> match(
        matchInt: ValueIntegerHandler<R>, matchBoolean: ValueBooleanHandler<R>,
        matchEnum: ValueEnumHandler<R>
    ): R? {
        return matchInt.handle(value)
    }

    fun equals(other: ValueInt?): Boolean {
        return other != null && value == other.value
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj !is ValueInt) {
            return false
        }

        return value == obj.value
    }

    override fun hashCode(): Int {
        return value
    }

    override fun toString(): String {
        return "ValueInt($value)"
    }

    override val type: Type
        get() = TypeInt.Companion.INT

    override val valueString: String
        get() = value.toString()
}
