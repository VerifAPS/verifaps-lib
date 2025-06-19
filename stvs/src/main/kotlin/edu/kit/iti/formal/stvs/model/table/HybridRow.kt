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

import javafx.beans.Observable
import javafx.collections.MapChangeListener
import javafx.util.Callback
import java.util.stream.Collectors

/**
 *
 * This is the model that is used by the
 * [edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController]'s
 * [javafx.scene.control.TableView] as rows. Unlike the rows of the
 * [ConstraintSpecification] these rows contain not [ConstraintCell]s, but
 * [HybridCell]s, so that both the constraint cells as well as counter example
 * values can be stored together in the model.
 *
 * @author Philipp
 */
class HybridRow(val sourceRow: SpecificationRow<ConstraintCell>, duration: ConstraintDuration?) :
    SpecificationRow<HybridCell<ConstraintCell>>(
        createCellsFromRow(sourceRow),
        Callback<HybridCell<ConstraintCell>, Array<Observable>> { hybridCell ->
            arrayOf(
                hybridCell.stringRepresentationProperty,
                hybridCell.commentProperty,
                hybridCell.counterExamplesProperty,
            )
        },
    ) {
    val duration = HybridCell(duration)

    /**
     * Creates an observable hybrid row that is synchronized to the state of the given sourceRow and
     * the duration.
     *
     * @param sourceRow the source row out of a [ConstraintSpecification] to synchronize this
     * row's hybrid cells for constraint cells to
     * @param duration the source constraint duration to synchronize this row's hybrid cell for the
     * duration to
     */
    init {
        sourceRow.cells.addListener(MapChangeListener { change -> this.onSourceCellsChange(change) })
        // Create bindings to all other stuff
        commentProperty.bindBidirectional(sourceRow.commentProperty)
    }

    private fun onSourceCellsChange(change: MapChangeListener.Change<out String?, out ConstraintCell>) {
        if (change.wasAdded()) {
            cells[change.key] = HybridCell(change.valueAdded)
        }
        if (change.wasRemoved()) {
            cells[change.key] = HybridCell(change.valueRemoved)
        }
    }

    /**
     * Updates the counterexample cells from the given concrete specification's row. If
     * the given [ConcreteSpecification] is empty, it will reset the counter example cells
     * list to the empty list.
     *
     * @param rowIndex the constraint row to look for cells
     * @param counterExample the concrete specification to look for counterexample values
     */
    fun updateCounterExampleCells(rowIndex: Int, counterExample: ConcreteSpecification?) {
        if (counterExample != null) {
            for ((key, value) in cells) {
                value!!.counterExamplesProperty
                    .setAll(createCounterExampleCells(key!!, rowIndex, counterExample))
            }
            val value: List<String> = counterExample.getConcreteDurationForConstraintRow(rowIndex)
                ?.duration?.toString().toSingleton() ?: listOf()
            duration.counterExamplesProperty.setAll(value)
        } else {
            duration.clearCounterExample()
        }
    }

    private fun createCounterExampleCells(
        columnId: String,
        rowIndex: Int,
        counterExample: ConcreteSpecification,
    ): List<String?> = counterExample.getConcreteValuesForConstraintCell(columnId, rowIndex).stream()
        .map { cell: ConcreteCell? -> cell!!.value.valueString }
        .collect(Collectors.toList())

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + (if (duration != null) duration.hashCode() else 0)
        result = 31 * result + (if (sourceRow != null) sourceRow.hashCode() else 0)
        return result
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }
        if (!super.equals(o)) {
            return false
        }

        val hybridRow = o as HybridRow

        if (if (duration != null) {
                duration != hybridRow.duration
            } else {
                hybridRow.duration != null
            }
        ) {
            return false
        }
        return if (sourceRow != null) sourceRow == hybridRow.sourceRow else hybridRow.sourceRow == null
    }

    companion object {
        private fun createCellsFromRow(
            subscribingRow: SpecificationRow<ConstraintCell>,
        ): Map<String, HybridCell<ConstraintCell>> {
            val cells = hashMapOf<String, HybridCell<ConstraintCell>>()
            for ((key, value) in subscribingRow.cells) {
                val hybridCell = HybridCell(value)
                cells[key] = hybridCell
            }
            return cells
        }
    }
}

private fun <T> T?.toSingleton() = if (this == null) null else listOf(this)