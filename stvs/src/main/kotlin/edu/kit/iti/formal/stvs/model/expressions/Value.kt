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
        matchInt: ValueIntegerHandler<R>,
        matchBoolean: ValueBooleanHandler<R>,
        matchEnum: ValueEnumHandler<R>,
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
        get() = TypeBool

    override val valueString: String
        get() = if (value) {
            "TRUE"
        } else {
            "FALSE"
        }

    override fun toString(): String = "ValueBool($value)"

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj !is ValueBool) {
            return false
        }

        return value == obj.value
    }

    override fun hashCode(): Int = (if (value) 1 else 0)

    companion object {
        @JvmField
        val TRUE: ValueBool = ValueBool(true)

        @JvmField
        val FALSE: ValueBool = ValueBool(false)

        @JvmStatic
        fun of(bool: Boolean): ValueBool = if (bool) TRUE else FALSE
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
    override fun toString(): String = "ValueInt($value)"

    override val type: Type
        get() = TypeInt

    override val valueString: String
        get() = value.toString()
}

/**
 * Runtime-representation for enum values of [Expression]s.
 * In contrast to [ValueBool] this is not a singleton, since many different instances can be
 * created at runtime. [ValueEnum.type] of this value always returns a [TypeEnum].
 * @param valueString enum constructor (for example `red`)
 * @param type enum type (for example `TypeEnum(COLORS, [red, green, blue])`)
 * @author Philipp
 */
data class ValueEnum(override val valueString: String, override val type: TypeEnum) : Value() {
    override fun toString() = "ValueEnum($valueString)"
}