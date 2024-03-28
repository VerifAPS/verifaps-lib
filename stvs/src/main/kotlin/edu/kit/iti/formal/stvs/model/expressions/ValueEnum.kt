package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation for enum values of [Expression]s.
 * In contrast to [ValueBool] this is not a singleton, since many different instances can be
 * created at runtime. [ValueEnum.getType] of this value always returns a [TypeEnum].
 *
 * @author Philipp
 */
class ValueEnum
/**
 * package-local. Generate values from TypeEnum! Construct a new value of given type with given
 * constructor.
 *
 * @param enumValue enum constructor (for example <tt>red</tt>)
 * @param enumType enum type (for example <tt>TypeEnum(COLORS, [red, green, blue])</tt>)
 */ internal constructor(override val valueString: String, override val type: TypeEnum) : Value {
    override fun <R> match(
        matchInt: ValueIntegerHandler<R>, matchBoolean: ValueBooleanHandler<R>,
        matchEnum: ValueEnumHandler<R>
    ): R? {
        return matchEnum.handle(this)
    }

    fun equals(other: ValueEnum?): Boolean {
        return other != null && valueString == other.valueString && type.equals(other.type)
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj !is ValueEnum) {
            return false
        }

        val valueEnum = obj

        if (valueString != valueEnum.valueString) {
            return false
        }
        return type.equals(valueEnum.type)
    }

    override fun hashCode(): Int {
        var result = valueString.hashCode()
        result = 31 * result + type.hashCode()
        return result
    }

    override fun toString(): String {
        return "ValueEnum(" + valueString + ")"
    }
}
