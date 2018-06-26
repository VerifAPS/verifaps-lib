package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.datatypes.values.RecordValue
import edu.kit.iti.formal.automation.datatypes.values.Value
import java.util.*

typealias EValue = Value<*, *>

class State(private val impl: MutableMap<String, EValue> = HashMap()/*val parent: State?*/)
    : MutableMap<String, EValue> by impl {
    fun declare(key: String, dataType: AnyDt) = declare(key, ExecutionFacade.getDefaultValue(dataType))
    fun <T : AnyDt, S : Any> declare(key: String, value: Value<T, S>) = impl.put(key, value)
    //operator fun get(name: String) = impl[name]
    operator fun contains(key: String) = key in impl

    operator fun get(name: List<String>): EValue? {
        if (name.isEmpty()) return null
        if (name.size == 1) return this[name[0]]
        try {
            val o = impl[name[0]] as Value<RecordType, RecordValue>
            val state = State(o.value.fieldValues)
            val r = 1..(name.size - 1)
            return state[name.slice(r)]
        } catch (e: ClassCastException) {
            return null
        }
    }

    operator fun contains(key: List<String>) = get(key) != null
    operator fun plusAssign(values: Map<String, EValue>) {
        impl += values
    }

    operator fun set(name: List<String>, value: EValue) {
        if (name.isEmpty()) return
        if (name.size == 1) this[name[0]] = value
        try {
            val o = impl[name[0]] as Value<RecordType, RecordValue>
            val state = State(o.value.fieldValues)
            val r = 1..(name.size-1)
            state[name.slice(r)] = value
        } catch (e: ClassCastException) {
            return
        }
    }

    operator fun set(name: String, value: EValue) {
        impl[name] = value
    }

    fun clone(): State {
        //TODO copy
        val s = State(HashMap(impl))
        return s
    }

    override fun toString(): String = map { (k, v) -> k to v }.toString()

}
