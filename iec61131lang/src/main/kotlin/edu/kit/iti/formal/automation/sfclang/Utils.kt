package edu.kit.iti.formal.automation.sfclang

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

import java.math.BigInteger
import java.util.*
import java.util.regex.Pattern

internal var PATTERN = Pattern.compile("((?<prefix>\\D\\w*?)#)?((?<radix>\\d+?)#)?(?<value>.*)")


private var uniqueNameId = 0
fun getUniqueName(prefix: String = "", postfix: String = "") = "$prefix${++uniqueNameId}$postfix"

fun split(s: String): Splitted {
    val t = PATTERN.matcher(s)
    return if (t.matches()) {
        Splitted(t.group("prefix"), t.group("radix"), t.group("value"))
    } else {
        throw IllegalArgumentException("Argument is not well word: expected form " + PATTERN.pattern())
    }
}

fun getIntegerLiteralValue(text: String, sign: Boolean): BigInteger {
    val s = split(text)
    return if (sign) s.number().negate() else s.number()
}

data class Splitted(
        val prefix: String? = null,
        val ordinal: String? = null,
        val value: String? = null) {

    fun number(): BigInteger {
        var r = 10
        if (ordinal != null) {
            r = Integer.parseInt(ordinal)
        }
        return BigInteger(value!!, r)
    }
}
