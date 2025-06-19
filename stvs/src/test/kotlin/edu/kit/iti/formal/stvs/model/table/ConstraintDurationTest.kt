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
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 25.02.17.
 */
class ConstraintDurationTest {
    private var duration: ConstraintDuration? = null

    @BeforeEach
    fun setUp() {
        duration = ConstraintDuration("[2,3]")
        duration!!.comment = "I am a comment!"
    }

    @Test
    fun testCopyConstructor() {
        val clone = ConstraintDuration(duration!!)
        Assertions.assertNotSame(clone, duration)
        Assertions.assertEquals(clone, duration)
    }

    @Test
    fun setFromString() {
        duration!!.setFromString("[4,-]")
        Assertions.assertEquals("[4,-]", duration!!.asString)
    }

    @Test
    fun equals() {
        val identical = ConstraintDuration("[2,3]")
        identical.comment = "I am a comment!"
        Assertions.assertEquals(identical, duration)
        Assertions.assertNotEquals(duration, null)
        identical.setFromString("[4,-]")
        Assertions.assertNotEquals(identical, duration)
    }
}