/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.model.expressions

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
        values.forEach(
            Consumer { valueName: String ->
                val valueEnum = ValueEnum(valueName, this)
                valueMap[valueName] = valueEnum
                valueList.add(valueEnum)
            },
        )
    }

    override fun checksAgainst(other: Type): Boolean = other.match(
        { false },
        { false },
        { otherEnum: TypeEnum? -> otherEnum!!.typeName == typeName },
    )

    override fun parseLiteral(literal: String): Value? = valueMap[literal]

    override fun generateDefaultValue(): Value = valueMap.values.iterator().next()

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

    fun equals(other: TypeEnum): Boolean = typeName == other.typeName

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

    override fun toString(): String = "TypeEnum(" + typeName + " : " + valueMap.keys + ")"
}