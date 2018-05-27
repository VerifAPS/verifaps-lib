package edu.kit.iti.formal.automation.datatypes.values

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

import edu.kit.iti.formal.automation.datatypes.AnyDate
import edu.kit.iti.formal.automation.sfclang.Utils
import lombok.*

import java.util.function.Function
import java.util.regex.Matcher
import java.util.regex.Pattern

/**
 *
 * TimeofDayData class.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
@NoArgsConstructor
class TimeofDayData {
    private val hours: Int
    private val minutes: Int
    private val seconds: Int
    private var millieseconds: Int

    constructor(hours: Int, minutes: Int, seconds: Int) {
        this.hours = hours
        this.minutes = minutes
        this.seconds = seconds
    }

    constructor(hour: Int, min: Int, sec: Int, ms: Int) : this(hour, min, sec) {
        millieseconds = ms
    }

    companion object {

        fun parse(tod: String): Value<AnyDate.TimeOfDay, TimeofDayData> {
            val pattern = Pattern.compile(
                    "(?<hour>\\d?\\d):(?<min>\\d?\\d)(:(?<sec>\\d?\\d))?(.(?<ms>\\d+))?")
            val s = Utils.split(tod)
            val matcher = pattern.matcher(s.value().get())
            val parseInt = { key: String ->
                val a = matcher.group(key)
                return if (a == null)
                    0
                else
                    Integer.parseInt(a)
            }

            if (matcher.matches()) {
                val hour = parseInt.apply("hour")
                val min = parseInt.apply("min")
                val sec = parseInt.apply("sec")
                val ms = parseInt.apply("ms")
                val t = TimeofDayData(hour, min, sec, ms)
                return Values.VToD(AnyDate.TIME_OF_DAY, t)
            } else {
                throw IllegalArgumentException("Given string is not a time of day value.")
            }
        }
    }
}
