/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 *
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
 * *****************************************************************/
package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.ArrayType

class NDArray<T : Any>(val dimensions: Array<IntRange>, defaultValue: T) {
    val spanDim = dimensions.map { it.last - it.first + 1 }.toTypedArray()
    val size = spanDim.reduce { a, b -> a * b }
    val facN by lazy {
        val ary = Array(spanDim.size) { 0 }
        ary[ary.size - 1] = 1
        for (k in (spanDim.size - 2) downTo 0) {
            ary[k] = ary[k + 1] * spanDim[k + 1]
        }
        ary
    }
    var data: Array<Any> = Array(size) { defaultValue }

    fun pos(seq: List<Int>): Int {
        // see https://en.wikipedia.org/wiki/Row-_and_column-major_order#Address_calculation_in_general
        return seq.zip(dimensions)
            .map { (a, b) -> a - b.first } // zero-base entries
            .zip(facN)
            .map { (a, b) -> a * b } // multiplicate with dimension factor
            .sum()
    }

    operator fun set(it: List<Int>, value: T) {
        val p = pos(it)
        // data.ensureCapacity(p + 1)
        data[p] = value
    }

    @Suppress("UNCHECKED_CAST")
    operator fun get(it: List<Int>): T = data[pos(it)] as T
    operator fun get(vararg idx: Int): T = this[idx.toList()]
    operator fun set(vararg idx: Int, value: T) {
        data[pos(idx.toList())] = value
    }
}

class MultiDimArrayValue(val arrayType: ArrayType, defaultValue: Value<*, *>) {

    private val array = NDArray(
        arrayType.ranges.map { it.startValue..it.stopValue }.toTypedArray(),
        defaultValue,
    )

    constructor(arrayType: ArrayType, defaultValue: Value<*, *>, initialValues: List<Value<*, *>>) :
        this(arrayType, defaultValue) {
        initialValues.forEachIndexed { idx, value -> array.data[idx] = value }
    }

    operator fun get(idx: List<Int>): Value<AnyDt, Any> = array[idx] as Value<AnyDt, Any>

    operator fun get(it: IntArray): Value<AnyDt, Any> = this[it.toList()]

    fun internalData() = array.data
}
