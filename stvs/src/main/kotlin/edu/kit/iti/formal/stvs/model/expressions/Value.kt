package edu.kit.iti.formal.stvs.model.expressions

/**
 * The common interface for values of Expressions. Values are visitable and have a type.
 *
 * @author Philipp
 */
sealed class Value {
    /**
     * Visitor function for Values. Subclasses call the respective Functions.
     *
     * @param matchInt a function for handling an integer value
     * @param matchBoolean a function for handling a boolean value
     * @param matchEnum a function for handling an enum value
     * @param <R> the return type of the visitor functions
     * @return the return value of the visitor function called
    </R> */
    fun <R> match(
        matchInt: ValueIntegerHandler<R>, matchBoolean: ValueBooleanHandler<R>, matchEnum: ValueEnumHandler<R>
    ): R = when (this) {
        is ValueBool -> matchBoolean.handle(this.value)
        is ValueEnum -> matchEnum.handle(this)
        is ValueInt -> matchInt.handle(this.value)
    }

    /**
     * Should return type of this value.
     * @return the type for this expression. (returns a TypeBool for a ValueInt for example)
     */
    abstract val type: Type

    /**
     * Should return a string representation of this value.
     * @return a String representation of the represented value
     */
    abstract val valueString: String
}


/**
 * Runtime-representation for boolean values of [Expression]s.
 * This is a singleton with two instances, TRUE and FALSE, since there is no state to the values.
 *
 * @author Philipp
 */
data class ValueBool(val value: Boolean) : Value() {
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


/**
 * Runtime-representation for integer values of [Expression]s.
 * This is not a singleton (in contrast to [ValueBool]), since many different instances can be
 * created at runtime.
 * @param value the integer this value should represent.
 * @author Philipp
 */
data class ValueInt(val value: Int) : Value() {
    override fun toString(): String {
        return "ValueInt($value)"
    }

    override val type: Type
        get() = TypeInt.Companion.INT

    override val valueString: String
        get() = value.toString()
}


/**
 * Runtime-representation for enum values of [Expression]s.
 * In contrast to [ValueBool] this is not a singleton, since many different instances can be
 * created at runtime. [ValueEnum.getType] of this value always returns a [TypeEnum].
 * @param enumValue enum constructor (for example <tt>red</tt>)
 *  @param enumType enum type (for example <tt>TypeEnum(COLORS, [red, green, blue])</tt>)
 * @author Philipp
 */
data class ValueEnum(override val valueString: String, override val type: TypeEnum) : Value() {
    override fun toString() = "ValueEnum($valueString)"
}
