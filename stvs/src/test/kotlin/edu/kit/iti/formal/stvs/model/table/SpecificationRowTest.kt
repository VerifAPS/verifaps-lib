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
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import javafx.collections.FXCollections
import javafx.util.Callback
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 * @author Philipp
 */
class SpecificationRowTest {
    private val toBeChanged: StringProperty = SimpleStringProperty("")
    private var specRow: SpecificationRow<StringProperty> = SpecificationRow(HashMap(), identityExtractor())
    private var listenerCalls = 0

    @BeforeEach
    fun setUp() {
        specRow = SpecificationRow(HashMap(), identityExtractor())
        specRow.cells["abc"] = toBeChanged
        listenerCalls = 0
    }

    @Test
    fun testInvalidationListener() {
        specRow.addListener { _: Observable? -> listenerCalls++ }

        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls before change")
        toBeChanged.set("XYZ")
        Assertions.assertEquals(1, listenerCalls.toLong(), "listener calls after change")
    }

    @Test
    fun testNestedRows() {
        val rows =
            FXCollections.observableList(
                listOf(specRow),
                identityExtractor(),
            )
        rows.addListener { _: Observable? -> listenerCalls++ }

        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls before change")
        toBeChanged.set("XXX")
        Assertions.assertEquals(1, listenerCalls.toLong(), "listener calls after change")

        val toBeAddedChangedRemoved: StringProperty = SimpleStringProperty("")

        rows[0]!!.cells["toBeAddedChangedRemoved"] = toBeAddedChangedRemoved
        Assertions.assertEquals(2, listenerCalls.toLong(), "listener calls after adding")

        toBeAddedChangedRemoved.set("ASDF")
        Assertions.assertEquals(3, listenerCalls.toLong(), "listener calls after changing added")

        rows[0]!!.cells.remove("toBeAddedChangedRemoved")
        Assertions.assertEquals(4, listenerCalls.toLong(), "listener calls after removing")

        toBeAddedChangedRemoved.set("SHOULD NOT FIRE EVENT")
        Assertions.assertEquals(4, listenerCalls.toLong(), "listener calls after changing cell that was removed")
    }

    @Test
    fun testUnobservableRow() {
        val cells = hashMapOf<String, StringProperty>()
        cells["abc"] = toBeChanged
        val unobservable: SpecificationRow<*> = SpecificationRow.createUnobservableRow(cells)
        unobservable.addListener { _: Observable? -> listenerCalls++ }
        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls before change")
        toBeChanged.set("XYZ")
        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls after change")
        cells["def"] = SimpleStringProperty("test")
        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls after add")
    }

    @Test
    fun testEquals() {
        val otherRow = SpecificationRow(HashMap(), identityExtractor())
        otherRow.cells["abc"] = toBeChanged
        Assertions.assertEquals(otherRow, specRow)
        Assertions.assertEquals(specRow, specRow)
        otherRow.cells["abc"] = SimpleStringProperty("something else")
        Assertions.assertNotEquals(otherRow, specRow)
        Assertions.assertNotEquals(specRow, null)
    }

    @Test
    fun testHashCode() {
        val toBeChanged: StringProperty = SimpleStringProperty("")

        val specRow = SpecificationRow(HashMap(), identityExtractor())
        specRow.cells["abc"] = toBeChanged

        val otherRow = SpecificationRow(HashMap(), identityExtractor())
        otherRow.cells["abc"] = toBeChanged

        Assertions.assertEquals(otherRow.hashCode(), specRow.hashCode())
        Assertions.assertEquals(otherRow, specRow)

        otherRow.cells["abd"] = SimpleStringProperty("something else")
        Assertions.assertNotEquals(otherRow.hashCode(), specRow.hashCode())
    }

    companion object {
        private fun <E : Observable> identityExtractor(): Callback<E, Array<Observable>> = Callback { arrayOf(it) }
    }
}