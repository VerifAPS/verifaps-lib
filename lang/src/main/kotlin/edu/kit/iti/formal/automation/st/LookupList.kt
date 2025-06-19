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
package edu.kit.iti.formal.automation.st

import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (09.05.18)
 */
interface LookupList<T> :
    MutableCollection<T>,
    Cloneable
    where T : Cloneable, T : Identifiable {
    operator fun get(name: String): T? = this[{ obj -> obj == name }]
    operator fun get(x: (String) -> Boolean): T? = find { x(it.name) }
    operator fun contains(name: String) = this[name] != null
    fun remove(element: String): Boolean {
        val obj = this[element]
        if (obj != null) return remove(obj)
        return false
    }

    fun removeAllByName(seq: Collection<String>) = seq.forEach { remove(it) }

    fun replace(name: String, variable: T): Boolean {
        remove(name)
        return add(variable)
    }

    override fun clone(): LookupList<T>
}

data class SetLookupList<T>(private val impl: TreeSet<T> = TreeSet({ a, b -> a.name.compareTo(b.name) })) :
    MutableSet<T> by impl,
    LookupList<T>
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

data class ArrayLookupList<T>(private val impl: ArrayList<T> = arrayListOf()) :
    MutableList<T> by impl,
    LookupList<T>
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