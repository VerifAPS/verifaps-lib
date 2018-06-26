package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.st.ast.Range

class MultiDimArrayValue() {
    var data: Array<Value<*, *>> = arrayOf()

    constructor(ranges: MutableList<Range>, init: Value<*, *>) : this() {
        val sz = ranges.map { it.stopValue - it.startValue + 1 }.reduce { a, b -> a * b }
        data = Array(sz, { init })
    }

    constructor(values: List<Value<*, *>>) : this() {
        data = values.toTypedArray()
    }


    fun get(x: Int): Unit {

    }


    fun set(x: Int): Unit {

    }

}
