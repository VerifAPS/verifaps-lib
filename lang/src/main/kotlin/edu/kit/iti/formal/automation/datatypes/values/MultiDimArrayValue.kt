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
        //see https://en.wikipedia.org/wiki/Row-_and_column-major_order#Address_calculation_in_general
        return seq.zip(dimensions)
                .map { (a, b) -> a - b.first } //zero-base entries
                .zip(facN)
                .map { (a, b) -> a * b } //multiplicate with dimension factor
                .sum()
    }

    operator fun set(it: List<Int>, value: T) {
        val p = pos(it)
        //data.ensureCapacity(p + 1)
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
            defaultValue)

    constructor(arrayType: ArrayType, defaultValue: Value<*, *>, initialValues: List<Value<*, *>>)
            : this(arrayType, defaultValue) {
        initialValues.forEachIndexed { idx, value -> array.data[idx] = value }
    }


    operator fun get(idx: List<Int>): Value<AnyDt, Any> {
        return array[idx] as Value<AnyDt, Any>
    }

    operator fun get(it: IntArray): Value<AnyDt, Any> {
        return this[it.toList()]
    }


    fun internalData() = array.data

}