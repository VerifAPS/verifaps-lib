package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.st.ast.Range

class MultiDimArrayValue(ranges: MutableList<Range>, init: Value<*, *>) {
    var data: Array<Value<*, *>>

    init {
        val sz = ranges.map { it.stopValue - it.startValue + 1 }.reduce { a, b -> a * b }
        data = Array(sz, { init })
    }


    fun get(x: Int): Unit {

    }


    fun set(x: Int): Unit {

    }

}
