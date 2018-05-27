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

import edu.kit.iti.formal.automation.sfclang.Utils.Splitted
import lombok.AllArgsConstructor
import lombok.ToString

import java.math.BigInteger
import java.util.Optional
import java.util.regex.Matcher
import java.util.regex.Pattern

/**
 *
 * Utils class.
 *
 * @author weigl
 * @version $Id: $Id
 */
object Utils {
    internal var PATTERN = Pattern.compile("((?<prefix>\\D\\w*?)#)?((?<radix>\\d+?)#)?(?<value>.*)")

    /**
     *
     * getRandomName.
     *
     * @return a [java.lang.String] object.
     */
    val randomName: String
        get() = "action_" + (Math.random() * 10000).toInt()


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

    @AllArgsConstructor
    @ToString
    class Splitted {
        private val prefix: String? = null
        private val ordinal: String? = null
        private val value: String? = null

        fun prefix(): Optional<String> {
            return if (prefix == null) Optional.empty() else Optional.of(prefix)
        }

        fun radix(): Optional<String> {
            return if (ordinal == null) Optional.empty() else Optional.of(ordinal)
        }

        fun value(): Optional<String> {
            return if (value == null) Optional.empty() else Optional.of(value)
        }

        fun number(): BigInteger {
            var r = 10
            if (ordinal != null) {
                r = Integer.parseInt(ordinal)
            }
            return BigInteger(value!!, r)
        }
    }
}
