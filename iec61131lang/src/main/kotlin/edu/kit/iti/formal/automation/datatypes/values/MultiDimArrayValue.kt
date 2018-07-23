package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.datatypes.ArrayType
import edu.kit.iti.formal.automation.st.DefaultInitValue

class MultiDimArrayValue(
        private val type: ArrayType,
        internal var data: ArrayList<Value<*, *>> = arrayListOf()) {

    constructor (arrayType: ArrayType, init: Value<*, *>) : this(arrayType, arrayListOf()) {
        arrayType.allIndices().forEach {
            data.add(init)
            //this[it] = init
        }
    }

    constructor(type: ArrayType) : this(type, DefaultInitValue.getInit(type.fieldType))


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
        val p = pos(it)
        data.ensureCapacity(p + 1)
        data[p] = value
    }

    operator fun get(it: List<Int>) = data[pos(it)]
}