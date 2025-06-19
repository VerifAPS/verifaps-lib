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
                newList,
            )
        }
        return observableList
    }
}