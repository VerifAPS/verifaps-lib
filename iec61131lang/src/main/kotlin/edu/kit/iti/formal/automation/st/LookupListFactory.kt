package edu.kit.iti.formal.automation.st

import lombok.RequiredArgsConstructor
import lombok.experimental.Delegate

import java.util.ArrayList

/**
 * @author Alexander Weigl
 * @version 1 (09.05.18)
 */
object LookupListFactory {
    fun <T : Identifiable> create(): LookupList<T> {
        return create(ArrayList())
    }

    fun <T : Identifiable> create(list: List<T>): LookupList<T> {
        return LookupListWrapper(list)
    }

    @RequiredArgsConstructor
    private class LookupListWrapper<T : Identifiable> : LookupList<T> {
        @Delegate
        private val seq: List<T>? = null
    }
}
