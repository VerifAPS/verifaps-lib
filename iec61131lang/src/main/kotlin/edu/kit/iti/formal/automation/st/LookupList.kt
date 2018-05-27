package edu.kit.iti.formal.automation.st

import java.util.Optional

/**
 * @author Alexander Weigl
 * @version 1 (09.05.18)
 */
interface LookupList<T : Identifiable> : MutableList<T> {
    operator fun get(name: String): Optional<T> {
        return stream().findFirst().filter { i -> i.name == name }
    }

    fun getIgnoreCase(name: String): Optional<T> {
        return stream().findFirst().filter { i -> i.name.equals(name, ignoreCase = true) }
    }
}
