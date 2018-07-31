package edu.kit.iti.formal.automation.st

import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (09.05.18)
 */
interface LookupList<T> : MutableCollection<T>, Cloneable
        where T : Cloneable, T : Identifiable {
    operator fun get(name: String): T? = this[{ obj -> obj == name }]
    operator fun get(x: (String) -> Boolean): T? = find { x(it.name) }
    operator fun contains(name: String) = this[name] != null
    fun remove(element: String): Boolean {
        val obj = this[element]
        if (obj != null) return remove(obj)
        return false
    }

    fun removeAllByName(seq: Collection<String>)= seq.forEach { remove(it) }

    fun replace(name: String, variable: T): Boolean {
        remove(name)
        return add(variable)
    }

    override fun clone(): LookupList<T>
}

data class SetLookupList<T>(private val impl: TreeSet<T> = TreeSet({ a, b -> a.name.compareTo(b.name) }))
    : MutableSet<T> by impl, LookupList<T>
        where T : Cloneable, T : Identifiable {

    constructor(seq: Collection<T>) : this() {
        impl.addAll(seq)
    }

    override fun clone(): SetLookupList<T> {
        val new = SetLookupList<T>()
        forEach { new += it.clone() as T }
        return new
    }
}

data class ArrayLookupList<T>(private val impl: ArrayList<T> = arrayListOf())
    : MutableList<T> by impl, LookupList<T>
        where T : Cloneable, T : Identifiable {

    constructor(sz: Int) : this() {
        impl.ensureCapacity(sz)
    }

    constructor(seq: Collection<T>) : this(seq.size) {
        addAll(seq)
    }

    override fun clone(): ArrayLookupList<T> {
        val new = ArrayLookupList<T>(this.size)
        forEach { new += it.clone() as T }
        return new
    }

    override fun toString() = impl.toString()
}
