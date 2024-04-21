package edu.kit.iti.formal.stvs.util

import javafx.beans.property.ObjectProperty
import javafx.beans.value.ObservableValue
import javafx.collections.FXCollections
import javafx.collections.ObservableList

/**
 * Util class for conversion of ObservableLists.
 *
 * @author Carsten Csiky
 */
object ListTypeConverter {
    /**
     * Creates a [ObservableList].
     *
     * @param list property of the list to convert
     * @param <E> type of the list elements
     * @return observable list
    </E> */
    @JvmStatic
    fun <E> makeObservableList(list: ObjectProperty<List<E>>): ObservableList<E> {
        val observableList = FXCollections.observableList(list.get())
        list.addListener { observableValue: ObservableValue<out List<E>?>?, oldList: List<E>?, newList: List<E>? ->
            observableList.setAll(
                newList
            )
        }
        return observableList
    }
}
