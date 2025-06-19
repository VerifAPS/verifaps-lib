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
package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.TestUtils
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by bal on 26.02.17.
 */
class ColumnConfigTest {
    private var config = ColumnConfig(130.0)

    @Test
    fun testGetSetColwidth() {
        // default colwidth
        assertEquals(100.0, ColumnConfig().width, TestUtils.EPSILON)
        assertEquals(130.0, config.width, TestUtils.EPSILON)
        config.width = 120.0
        assertEquals(120.0, config.width, TestUtils.EPSILON)
    }

    @Test
    fun testIllegalColwidthConstructor() {
        assertFailsWith<IllegalArgumentException> {
            config = ColumnConfig(0.0)
        }
    }

    @Test
    fun testSetIllegalWidth() {
        assertFailsWith<IllegalArgumentException> {
            config.width = (-1).toDouble()
        }
    }

    @Test
    fun testEquals() {
        val identical = ColumnConfig(130.0)
        assertEquals(identical, config)
        Assertions.assertNotEquals(null, config)
        assertEquals(config, config)
        identical.width = 100.0
        Assertions.assertNotEquals(identical, config)
    }

    @Test
    fun testHashCode() {
        val identical = ColumnConfig(130.0)
        assertEquals(identical.hashCode().toLong(), config.hashCode().toLong())
        assertEquals(config.hashCode().toLong(), config.hashCode().toLong())
        identical.width = 100.0
        Assertions.assertNotEquals(identical.hashCode().toLong(), config.hashCode().toLong())
    }
}