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
package edu.kit.iti.formal.stvs.model.common

import javafx.beans.InvalidationListener
import javafx.beans.Observable
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * Created by leonk on 18.01.2017.
 */
class SelectionTest {
    @Test
    fun testClearColumnListenerSelection() {
        val wasCalled: BooleanProperty = SimpleBooleanProperty(false)
        val selection = Selection("fgrfg", 4)
        val listener = InvalidationListener { i: Observable? -> wasCalled.set(true) }
        selection.columnProperty.addListener(listener)
        selection.columnProperty.set(null)
        Assertions.assertTrue(wasCalled.get())
        Assertions.assertTrue(selection.columnProperty.isNull().get())

        wasCalled.set(false)
        selection.columnProperty.removeListener(listener)
        selection.column = ("Test")
        Assertions.assertFalse(wasCalled.get())
        Assertions.assertEquals("Test", selection.column)
    }

    @Test
    fun testSetRow() {
        val selection = Selection()
        Assertions.assertTrue(selection.rowProperty.isNull().get())
        selection.row = (5)
        Assertions.assertEquals(5, selection.row?.toLong())
        Assertions.assertEquals(5, selection.row?.toLong())
    }
}