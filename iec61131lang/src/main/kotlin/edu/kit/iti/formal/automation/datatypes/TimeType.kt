package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.values.TimeData

/**
 *
 * TimeType class.
 *
 * @author weigl
 * @version $Id: $Id
 */
/**
 *
 * Constructor for TimeType.
 */
class TimeType : AnyDt("TIME") {

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String {
        val time = obj as TimeData
        val stb = StringTimeBuilder()
        stb.add(time.days.toDouble(), "d")
        stb.add(time.hours.toDouble(), "h")
        stb.add(time.minutes.toDouble(), "m")
        stb.add(time.seconds.toDouble(), "s")
        stb.add(time.milliseconds.toDouble(), "ms")
        return stb.sb.toString()
        /**
         *
         * add.
         *
         * @param value a double.
         * @param unit a [java.lang.String] object.
         */
    }

    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }

    companion object {
        /** Constant `TIME_TYPE`  */
        val TIME_TYPE = TimeType()
        val LTIME_TYPE = TimeType()
    }
}

internal class StringTimeBuilder {
    var sb = StringBuilder("TIME#")

    fun add(value: Double, unit: String) {
        if (value != 0.0) {
            sb.append(value).append(unit)
        }
    }
}
