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

import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.expressions.ValueInt
import javafx.beans.property.SimpleStringProperty
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class ConcreteCellTest {
    private var cellA = ConcreteCell(ValueInt(4))

    @Test
    fun testGetValue() {
        Assertions.assertEquals(ValueInt(4), cellA.value)
    }

    @Test
    fun testToString() {
        Assertions.assertEquals("ValueInt(4)", cellA.toString())
    }

    @Test
    fun testGetAsString() {
        Assertions.assertEquals("ValueInt(4)", cellA.asString)
    }

    @Test
    fun testStringRepresentationProperty() {
        Assertions.assertEquals(SimpleStringProperty("ValueInt(4)").get(), cellA.stringRepresentationProperty.get())
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val cellB = ConcreteCell(ValueInt(4))
        Assertions.assertEquals(cellA, cellB)
        val cellC = ConcreteCell(ValueInt(2))
        Assertions.assertNotEquals(cellA, cellC)
        val cellD = ConcreteCell(ValueBool.TRUE)
        Assertions.assertNotEquals(cellA, cellD)
        val cellE = ConstraintCell("4")
        Assertions.assertNotEquals(cellA, cellE)
        Assertions.assertNotEquals(cellA, null)
    }
}