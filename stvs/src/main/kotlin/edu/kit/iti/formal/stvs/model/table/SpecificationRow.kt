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
package edu.kit.iti.formal.stvs.model.table

import javafx.beans.InvalidationListener
import javafx.beans.Observable
import javafx.beans.property.SimpleStringProperty
import javafx.collections.FXCollections
import javafx.collections.MapChangeListener
import javafx.collections.ObservableMap
import javafx.util.Callback
import java.util.Objects
import java.util.function.Consumer
import java.util.stream.Collectors

/**
 * A row in a specification table (see [SpecificationTable]). The generic type parameter C is
 * the type of the cells.
 *
 * @author Benjamin Alt
 */
open class SpecificationRow<C>(cells: Map<String, C>, val extractor: Callback<C, Array<Observable>>) :
    Commentable,
    Observable {

    val cells: ObservableMap<String, C> = FXCollections.observableMap(cells)
    override var commentProperty = SimpleStringProperty()
    private val listeners: MutableList<InvalidationListener> = arrayListOf()

    /**
     * Create a SpecificationRow from a given number of cells and an extractor. The extractor is
     * required for "deep observing", i.e. the registering of change listeners on the contents of an
     * observable collection (here, the collection of cells - to fire change events not only when
     * cells are added or removed, but also when properties in the cells change). For more information
     * on extractors, see https://docs.oracle
     * .com/javase/8/javafx/api/javafx/collections/FXCollections.html.
     *
     * @param cells The initial cells of the row
     * @param extractor The extractor to be used for deep observing on the cells
     */
    init {
        this.cells.addListener(MapChangeListener { change -> this.cellsMapChanged(change) })
        this.cells.addListener { observable: Observable -> this.listenRowInvalidation(observable) }
        commentProperty.addListener { observable: Observable -> this.listenRowInvalidation(observable) }
        cells.values.forEach(Consumer { c: C -> this.subscribeToCell(c) })
    }

    private fun listenRowInvalidation(observable: Observable) {
        listeners.forEach(Consumer { listener: InvalidationListener -> listener.invalidated(observable) })
    }

    /**
     * Called when cells were added or removed to this row.
     *
     * @param change The change event
     */
    private fun cellsMapChanged(change: MapChangeListener.Change<out String?, out C?>) {
        if (change.wasAdded()) {
            subscribeToCell(change.valueAdded)
        }
        if (change.wasRemoved()) {
            unsubscribeFromCell(change.valueRemoved)
        }
    }

    /**
     * Add an InvalidationListener to a certain cell.
     *
     * @param c The cell to add a listener to
     */
    private fun subscribeToCell(c: C?) {
        for (observable in extractor.call(c)!!) {
            observable.addListener { observable: Observable -> this.listenRowInvalidation(observable) }
        }
    }

    /**
     * Remove an InvalidationListener from a certain cell.
     *
     * @param cell The cell to remove the listener from
     */
    private fun unsubscribeFromCell(cell: C?) {
        for (observable in extractor.call(cell)!!) {
            observable.removeListener { observable: Observable -> this.listenRowInvalidation(observable) }
        }
    }

    override fun toString(): String {
        val map = java.lang.String.join(
            ", ",
            cells.entries.stream()
                .map { entry: Map.Entry<String?, C> -> entry.key + ": " + entry.value }.collect(Collectors.toList()),
        )
        return "SpecificationRow(comment: " + comment + ", " + map + ")"
    }

    override fun addListener(listener: InvalidationListener) {
        listeners.add(listener)
    }

    override fun removeListener(listener: InvalidationListener) {
        listeners.remove(listener)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is SpecificationRow<*>) return false

        if (cells != other.cells) return false
        if (comment != other.comment) return false

        return true
    }

    override fun hashCode(): Int = Objects.hash(cells, comment)

    companion object {
        /**
         * Create a row which is not observable. This is the case for rows in
         * [ConcreteSpecification]s and implemented via an empty extractor.
         *
         * @param cells The cells of the unobservable row
         * @param <E> The type of the cells in the unobservable row
         * @return The created unobservable row
         </E> */
        fun <E> createUnobservableRow(cells: Map<String, E>): SpecificationRow<E> =
            SpecificationRow(cells) { arrayOf() }
    }
}