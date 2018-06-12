package edu.kit.iti.formal.automation

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

import java.io.BufferedReader
import java.io.IOException
import java.io.InputStreamReader
import java.util.*

/**
 * Created by weigl on 14.11.16.
 */
object TestUtils {


    @Throws(IOException::class)
    fun loadLines(filename: String): Iterable<Array<Any>> {
        val validExpression = ArrayList<Array<Any>>(4096)
        val ve = TestUtils::class.java.getResourceAsStream(filename)

        if (ve == null) {
            System.err.println("Could not find: $filename")
            return validExpression
        }

        val stream = BufferedReader(InputStreamReader(ve))
        stream.forEachLine {
            if (!it.startsWith("#"))
                validExpression.add(arrayOf(it))
        }

        println("Found: " + filename + " with " + validExpression.size + " lines!")
        return validExpression
    }

    fun asParameters(cases: Array<String>): List<Array<Any>> {
        return cases.map { arrayOf(it as Any) }
    }
}
