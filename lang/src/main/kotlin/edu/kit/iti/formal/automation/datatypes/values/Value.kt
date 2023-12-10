package edu.kit.iti.formal.automation.datatypes.values

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.st.ast.*
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
sealed class Value<T : AnyDt, S : Any>(
        val dataType: T, val value: S) {

    operator fun component1() = dataType
    operator fun component2() = value

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Value<*, *>) return false

        if (dataType != other.dataType) return false
        if (value != other.value) return false

        return true
    }

    override fun hashCode(): Int {
        var result = dataType.hashCode()
        result = 31 * result + value.hashCode()
        return result
    }

    override fun toString(): String {
        return "Value{$dataType}($value)"
    }

    open fun assignTo(ref: SymbolicReference): StatementList? = null
}


class VAnyInt(dt: AnyInt, v: BigInteger) : Value<AnyInt, BigInteger>(dt, v) {
    constructor(dt: AnyInt, v: Long) : this(dt, BigInteger.valueOf(v))

    override fun assignTo(ref: SymbolicReference): StatementList? = StatementList(ref assignTo IntegerLit(dataType, value))
}

class VClass(dt: ClassDataType, v: Map<String, Value<*, *>>)
    : Value<ClassDataType, Map<String, Value<*, *>>>(dt, v) {
}

class VAnyReal(dt: AnyReal, v: BigDecimal) : Value<AnyReal, BigDecimal>(dt, v) {
    override fun assignTo(ref: SymbolicReference): StatementList? = StatementList(ref assignTo RealLit(dataType, value))
}

class VAnyBit(dt: AnyBit, v: Bits) : Value<AnyBit, Bits>(dt, v) {
    override fun assignTo(ref: SymbolicReference) =
            StatementList(ref assignTo BitLit(dataType, value.register))
}

class VBool(dt: AnyBit.BOOL, v: Boolean) : Value<AnyBit.BOOL, Boolean>(dt, v) {
    override fun assignTo(ref: SymbolicReference) = StatementList(ref assignTo if (value) BooleanLit.LTRUE else BooleanLit.LFALSE)
}

val TRUE = VBool(AnyBit.BOOL, true)
val FALSE = VBool(AnyBit.BOOL, false)

class VIECString(dt: IECString, v: String) : Value<IECString, String>(dt, v) {
    override fun assignTo(ref: SymbolicReference) =
            StatementList(ref assignTo StringLit(dataType, value))
}

class VDate(dt: AnyDate.DATE, v: DateData) : Value<AnyDate.DATE, DateData>(dt, v) {
    override fun assignTo(ref: SymbolicReference) = StatementList(ref assignTo DateLit(value))
}

class VTime(dt: TimeType, v: TimeData) : Value<TimeType, TimeData>(dt, v) {
    override fun assignTo(ref: SymbolicReference) = StatementList(ref assignTo TimeLit(value))
}

class VDateAndTime(dt: AnyDate.DATE_AND_TIME, v: DateAndTimeData) : Value<AnyDate.DATE_AND_TIME, DateAndTimeData>(dt, v) {
    override fun assignTo(ref: SymbolicReference) = StatementList(ref assignTo DateAndTimeLit(value))

}

class VTimeOfDay(dt: AnyDate.TIME_OF_DAY, v: TimeofDayData) : Value<AnyDate.TIME_OF_DAY, TimeofDayData>(dt, v) {
    override fun assignTo(ref: SymbolicReference): StatementList? = StatementList(ref assignTo ToDLit(value))
}

class VAnyEnum(dt: EnumerateType, v: String) : Value<EnumerateType, String>(dt, v.uppercase(Locale.getDefault())) {
    override fun assignTo(ref: SymbolicReference) = StatementList(ref assignTo EnumLit(dataType, value))
}

class VStruct(dt: RecordType, v: RecordValue) : Value<RecordType, RecordValue>(dt, v) {
    val fieldValues: List<Pair<String, Value<*, *>>>
        get() {
            return dataType.fields.map {
                val specificValue = value.fieldValues[it.name]
                it.name to (specificValue ?: it.initValue
                ?: throw IllegalStateException("value it not determined for record value: field '${it.name}'"))
            }
        }

    override fun assignTo(ref: SymbolicReference): StatementList? {
        val seq = StatementList()
        fieldValues.forEach { (n, dt) ->
            dt.assignTo(ref[n])?.also {
                seq.addAll(it)
            }
        }
        return seq
    }
}


class VArray(dt: ArrayType, v: MultiDimArrayValue) : Value<ArrayType, MultiDimArrayValue>(dt, v) {
    override fun assignTo(ref: SymbolicReference): StatementList? {
        val seq = StatementList()
        val avalue = value
        dataType.allIndices().forEach {
            val svalue = avalue[it] as Value<*, *>
            svalue.assignTo(ref[it])?.also {
                seq.addAll(it)
            }
        }
        return seq
    }
}

object VVOID : Value<VOID, Unit>(VOID, Unit)
object VNULL : Value<ClassDataType.AnyClassDt, Unit>(ClassDataType.AnyClassDt, Unit) {
    override fun assignTo(ref: SymbolicReference) = StatementList(ref assignTo NullLit())
}
