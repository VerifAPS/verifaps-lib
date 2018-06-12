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

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */

import java.math.BigDecimal
import java.util.regex.Pattern

data class TimeData(var internal: BigDecimal = BigDecimal.ZERO) {
    val milliseconds: Long
        get() = internal.toLong()

    val seconds: Long
        get() = 0

    val minutes: Long
        get() = 0

    val hours: Long
        get() = 0

    val days: Long
        get() = 0

    constructor(textValue: String) : this() {
        var textValue = textValue
        textValue = textValue.replace("_", "")
        val extractNumbers = Pattern.compile("([.0-9]+)([hmsd]{1,2})")
        val matcher = extractNumbers.matcher(textValue)

        while (matcher.find()) {
            val num = matcher.group(1)
            val mod = matcher.group(2)
            val factor = getModifier(mod)
            internal = internal.add(BigDecimal.valueOf(factor * java.lang.Double.parseDouble(num)))
        }
    }

    constructor(time: Double) : this() {
        internal = BigDecimal.valueOf(time)
    }

    private fun getModifier(mod: String): Double {
        when (mod) {
            "d" -> return FACTOR_DAY.toDouble()
            "h" -> return FACTOR_HOUR.toDouble()
            "m" -> return FACTOR_MINUTE.toDouble()
            "s" -> return FACTOR_SECONDS.toDouble()
            "ms" -> return FACTOR_MILLISECONDS.toDouble()
            else -> return 0.0
        }
    }

    companion object {
        val FACTOR_MILLISECONDS = 1
        val FACTOR_SECONDS = 1000 * FACTOR_MILLISECONDS
        val FACTOR_MINUTE = 60 * FACTOR_SECONDS
        val FACTOR_HOUR = 60 * FACTOR_MINUTE
        val FACTOR_DAY = 24 * FACTOR_HOUR
    }
}
