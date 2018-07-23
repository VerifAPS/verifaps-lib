package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.datatypes.ArrayType

class MultiDimArrayValue(
        private val type: ArrayType,
        private var data: ArrayList<Value<*, *>> = arrayListOf()) {

    constructor (arrayType: ArrayType, init: Value<*, *>) : this(arrayType) {
        arrayType.allIndices().forEach { this[it] = init }
    }

    constructor(type: ArrayType, v: List<Value<*, *>>) : this(type) {
        data.addAll(v)
    }

    fun pos(seq: List<Int>): Int {
        //see https://en.wikipedia.org/wiki/Row-_and_column-major_order#Address_calculation_in_general
        val d = seq.size

        var sum = 0
        for (k in 0 until d) {
            var prod = 1
            for (l in (k + 1) until d) {
                prod *= type.dimSize(l)
            }
            sum += prod * seq[k]
        }
        return sum
    }

    operator fun set(it: List<Int>, value: Value<*, *>) {
        data[pos(it)] = value
    }

    operator fun get(it: List<Int>) = data[pos(it)]
}