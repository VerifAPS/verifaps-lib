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
import java.math.BigDecimal
import java.math.BigInteger

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
sealed class Value<T : AnyDt, S : Any>(
        val dataType: T, val value: S
)


class VAnyInt(dt: AnyInt, v: BigInteger) : Value<AnyInt, BigInteger>(dt, v)

class VClass(dt: ClassDataType, v: Map<String, Value<*, *>>)
    : Value<ClassDataType, Map<String, Value<*, *>>>(dt, v)

class VAnyReal(dt: AnyReal, v: BigDecimal) : Value<AnyReal, BigDecimal>(dt, v)
class VAnyBit(dt: AnyBit, v: Bits) : Value<AnyBit, Bits>(dt, v)

class VBool(dt: AnyBit.BOOL, v: Boolean) : Value<AnyBit.BOOL, Boolean>(dt, v)

val TRUE = VBool(AnyBit.BOOL, true)
val FALSE = VBool(AnyBit.BOOL, false)

class VIECString(dt: IECString, v: String) : Value<IECString, String>(dt, v)
class VDate(dt: AnyDate.DATE, v: DateData) : Value<AnyDate.DATE, DateData>(dt, v)
class VTime(dt: TimeType, v: TimeData) : Value<TimeType, TimeData>(dt, v)
class VDateAndTime(dt: AnyDate.DATE_AND_TIME, v: DateAndTimeData) : Value<AnyDate.DATE_AND_TIME, DateAndTimeData>(dt, v)
class VTimeOfDay(dt: AnyDate.TIME_OF_DAY, v: TimeofDayData) : Value<AnyDate.TIME_OF_DAY, TimeofDayData>(dt, v)
class VAnyEnum(dt: EnumerateType, v: String) : Value<EnumerateType, String>(dt, v)
class VToD(dt: AnyDate.TIME_OF_DAY, v: TimeofDayData) : Value<AnyDate.TIME_OF_DAY, TimeofDayData>(dt, v)
class VStruct(dt: RecordType, v: RecordValue) : Value<RecordType, RecordValue>(dt, v)
class VArray(dt: ArrayType, v: MultiDimArrayValue) : Value<ArrayType, MultiDimArrayValue>(dt, v)

object VVOID : Value<AnyDt.VOID, Unit>(AnyDt.VOID, Unit)
