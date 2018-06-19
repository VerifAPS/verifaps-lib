package edu.kit.iti.formal.automation.st

/**
 * @author Alexander Weigl
 * @version 1 (09.05.18)
 */
class LookupList<T>(private val impl: ArrayList<T> = arrayListOf()) : MutableCollection<T> by impl
        where T : Cloneable, T : Identifiable {

    constructor(sz: Int) : this() {
        impl.ensureCapacity(sz)
    }

    constructor(seq: Collection<T>) : this(seq.size) {
        addAll(seq)
    }

    operator fun get(name: String): T? = this[{ obj -> obj == name }]
    operator fun get(x: (String) -> Boolean): T? = find { x(it.name) }
    fun getIgnoreCase(name: String) =
            this[{ obj -> obj.equals(name, ignoreCase = true) }]

    operator fun contains(name: String) = this[name] != null
    fun remove(element: String): Boolean {
        val obj = this[element]
        if (obj != null) return remove(obj)
        return false
    }

    fun replace(name: String, variable: T): Boolean {
        remove(name)
        return add(variable)
    }

    fun clone(): LookupList<T> {
        val new = LookupList<T>(this.size)
        forEach { new += it.clone() as T }
        return new
    }

    override fun toString() = impl.toString()
}
