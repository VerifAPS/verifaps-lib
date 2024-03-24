package edu.kit.iti.formal.stvs.model.expressions

import java.util.*
import java.util.function.Consumer

/**
 * Runtime-representation for enum types. This is (in contrast to [TypeInt] or
 * [TypeBool]) NOT a singleton, since different instances of this can be created at runtime.
 *
 * @author Philipp
 */
class TypeEnum(enumTypeName: String, values: List<String>) : Type {
    override val typeName: String
    private val valueMap: MutableMap<String, ValueEnum>
    private val valueList: MutableList<ValueEnum>

    /**
     * Create a new enum-type. This should only happen, when an enum is parsed in st-code. St-code
     * example definition of an enum: <tt>COLORS : (red, green, blue)</tt>
     *
     * @param enumTypeName the type name (<tt>COLORS</tt> in this example)
     * @param values the possible values that this enum can be ([<tt>red</tt>, <tt>green</tt>,
     * <tt>blue</tt>] in this example)
     * @throws IllegalArgumentException if the given list of values is empty
     */
    init {
        require(!values.isEmpty()) { "Cannot create enum \"$enumTypeName\" without any values." }
        this.typeName = enumTypeName
        this.valueMap = HashMap()
        this.valueList = ArrayList()
        values.forEach(Consumer { valueName: String ->
            val valueEnum = ValueEnum(valueName, this)
            valueMap[valueName] = valueEnum
            valueList.add(valueEnum)
        })
    }

    override fun <R> match(
        matchIntType: TypeIntegerHandler<R>, matchBoolType: TypeBooleanHandler<R>,
        matchEnumType: TypeEnumHandler<R>
    ): R? {
        return matchEnumType.handle(this)
    }

    override fun checksAgainst(other: Type): Boolean {
        return other.match({ false }, { false },
            { otherEnum: TypeEnum? -> otherEnum!!.typeName == typeName })!!
    }

    override fun parseLiteral(literal: String): Optional<Value> {
        return Optional.ofNullable(valueMap[literal])
    }

    override fun generateDefaultValue(): Value {
        return valueMap.values.iterator().next()
    }

    val values: List<ValueEnum>
        get() = valueList

    /**
     * Returns a value of this enum that is resolved by name.
     *
     * @param enumName Name of the value
     * @return Value identified by the given name
     */
    fun valueOf(enumName: String): ValueEnum {
        val enumVal = valueMap[enumName]
        if (enumVal == null) {
            throw RuntimeException("No enum value \"$enumName\" for enum type: $this")
        } else {
            return enumVal
        }
    }

    fun equals(other: TypeEnum): Boolean {
        return typeName == other.typeName
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj !is TypeEnum) {
            return false
        }

        val typeEnum = obj

        if (typeName != typeEnum.typeName) {
            return false
        }
        return valueMap.keys == typeEnum.valueMap.keys
    }

    override fun hashCode(): Int {
        var result = typeName.hashCode()
        result = 31 * result + valueMap.keys.hashCode()
        return result
    }

    override fun toString(): String {
        return "TypeEnum(" + typeName + " : " + valueMap.keys + ")"
    }
}
