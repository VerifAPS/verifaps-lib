/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.model.options


import edu.kit.iti.formal.automation.testtables.model.Duration
import java.util.*

/**
 * Created by weigl on 16.12.16.
 */
class ConcreteTableOptions : InitializableFromProperties {
    private val stepCounter = TreeMap<String, Int>()

    fun getCount(step: String, defaultValue: Duration): Int {
        return stepCounter[step] ?: when (defaultValue) {
            is Duration.Omega -> 10
            is Duration.OpenInterval -> defaultValue.lower
            is Duration.ClosedInterval -> (defaultValue.lower + defaultValue.upper) / 2
        }
    }

    override fun initialize(namespace: String, p: Properties) {
        val nslength = namespace.length + 1
        for ((key1, value) in p) {
            val key = key1.toString()
            if (key.startsWith(namespace)) {
                val step = key.substring(nslength)
                val count = Integer.parseInt(value.toString())
                stepCounter[step] = count
            }
        }
    }
}
