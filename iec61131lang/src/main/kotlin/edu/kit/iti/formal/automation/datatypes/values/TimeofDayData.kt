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

import edu.kit.iti.formal.automation.sfclang.split
import java.util.regex.Pattern

/**
 *
 * TimeofDayData class.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class TimeofDayData(var hours: Int = 0, var minutes: Int = 0,
                         var seconds: Int = 0, var millieseconds: Int = 0) {
    companion object {
        fun parse(tod: String): TimeofDayData {
            val pattern = Pattern.compile(
                    "(?<hour>\\d?\\d):(?<min>\\d?\\d)(:(?<sec>\\d?\\d))?(.(?<ms>\\d+))?")
            val s = split(tod)
            val matcher = pattern.matcher(s.value!!)
            val parseInt = { key: String ->
                val a = matcher.group(key)
                if (a == null) 0 else Integer.parseInt(a)
            }

            if (matcher.matches()) {
                val hour = parseInt("hour")
                val min = parseInt("min")
                val sec = parseInt("sec")
                val ms = parseInt("ms")
                val t = TimeofDayData(hour, min, sec, ms)
                return t
            } else {
                throw IllegalArgumentException("Given string isType not a time of day value.")
            }
        }
    }
}
