package edu.kit.iti.formal.automation.datatypes.values

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
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
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
abstract class Values {

    class VClass(dataType: ClassDataType, value: Map<String, Value<*, *>>) : Value<ClassDataType, Map<String, Value<*, *>>>(dataType, value)

    class VAnyInt(dataType: AnyInt, value: BigInteger) : Value<AnyInt, BigInteger>(dataType, value)

    class VAnyReal(dataType: AnyReal, value: BigDecimal) : Value<AnyReal, BigDecimal>(dataType, value)

    class VAnyBit(dataType: AnyBit, value: Bits) : Value<AnyBit, Bits>(dataType, value)

    class VBool(dataType: AnyBit.Bool, value: Boolean?) : Value<AnyBit.Bool, Boolean>(dataType, value) {
        companion object {
            val TRUE: Value<*, *> = VBool(AnyBit.BOOL, true)
            val FALSE: Value<*, *> = VBool(AnyBit.BOOL, false)
        }
    }

    class VIECString(dataType: IECString, value: String) : Value<IECString, String>(dataType, value)

    class VDate(dataType: AnyDate.Date, value: DateData) : Value<AnyDate.Date, DateData>(dataType, value)

    class VTime(dataType: TimeType, value: TimeValue) : Value<TimeType, TimeValue>(dataType, value)

    class VDateAndTime(dataType: AnyDate.DateAndTime, value: DateAndTimeData) : Value<AnyDate.DateAndTime, DateAndTimeData>(dataType, value)

    class VAnyEnum(enumerateType: EnumerateType, value: String) : Value<EnumerateType, String>(enumerateType, value)

    class VToD(timeOfDay: AnyDate.TimeOfDay, t: TimeofDayData) : Value<AnyDate.TimeOfDay, TimeofDayData>(timeOfDay, t)
}
