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

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class ConcreteDurationTest {
    private var durationA = ConcreteDuration(1, 2)

    @Test
    fun testGetDuration() {
        Assertions.assertEquals(2, durationA.duration.toLong())
    }

    @Test
    fun testGetBeginCycle() {
        Assertions.assertEquals(1, durationA.beginCycle.toLong())
    }

    @Test
    fun testToString() {
        Assertions.assertEquals("2", durationA.toString())
    }

    @Test
    fun testGetEndCycle() {
        var duration = ConcreteDuration(3, 4)
        Assertions.assertEquals(7, duration.endCycle.toLong())
        duration = ConcreteDuration(0, 0)
        Assertions.assertEquals(0, duration.endCycle.toLong())
        duration = ConcreteDuration(1, 0)
        Assertions.assertEquals(1, duration.endCycle.toLong())
    }

    @Test // (expected = IllegalArgumentException::class)
    fun testConstructorInvalidBeginCycle() {
        assertFailsWith<IllegalArgumentException> {
            ConcreteDuration(-1, 1)
        }
    }

    @Test // (expected = IllegalArgumentException::class)
    fun testConstructorInvalidDuration() {
        assertFailsWith<IllegalArgumentException> {
            ConcreteDuration(1, -1)
        }
    }

    @Test
    fun testEquals() {
        val durationB = ConcreteDuration(1, 2)
        Assertions.assertEquals(durationA, durationB)
        val durationC = ConcreteDuration(1, 3)
        Assertions.assertNotEquals(durationA, durationC)
        val durationD = ConcreteDuration(2, 2)
        Assertions.assertNotEquals(durationA, durationD)
        val durationE = ConstraintDuration("2")
        Assertions.assertNotEquals(durationA, durationE)
        Assertions.assertNotEquals(durationA, null)
    }
}