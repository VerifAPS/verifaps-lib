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

/**
 * Created by bal on 25.02.17.
 */
class ConstraintCellTest {
    private var constraintCell = ConstraintCell("Test")
        .also {
            it.comment = "I am a comment!"
        }

    @Test
    fun testCopyConstructor() {
        val clone = ConstraintCell(constraintCell)
        Assertions.assertNotSame(constraintCell, clone)
        Assertions.assertEquals(constraintCell, clone)
    }

    @Test
    fun testEquals() {
        val identical = ConstraintCell("Test")
        identical.comment = "I am a comment!"
        Assertions.assertEquals(constraintCell, identical)
        Assertions.assertNotEquals(constraintCell, null)
        Assertions.assertNotEquals(constraintCell, ConstraintCell("Test"))
    }

    @Test
    fun testToString() {
        Assertions.assertEquals("Test (comment: \"I am a comment!\")", constraintCell.toString())
    }

    @Test
    fun testSetFromString() {
        constraintCell!!.setFromString("Some string")
        Assertions.assertEquals("Some string", constraintCell!!.asString)
    }
}