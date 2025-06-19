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
 * Created by bal on 26.02.17.
 */
class SpecificationColumnTest {
    private val column = SpecificationColumn(mutableListOf(1, 2, 3, 4, 5))

    @Test
    fun testEquals() {
        val column = SpecificationColumn(mutableListOf(1, 2, 3, 4, 5))
        val identical: SpecificationColumn<*> = SpecificationColumn(mutableListOf(1, 2, 3, 4, 5))
        Assertions.assertEquals(identical, column)
        column.comment = "Comment"
        Assertions.assertNotEquals(identical, column)
        identical.comment = "Comment"
        Assertions.assertEquals(identical, column)
        identical.comment = "Different comment"
        Assertions.assertNotEquals(identical, column)
        Assertions.assertNotEquals(null, column)
        Assertions.assertEquals(column, column)
    }

    @Test
    fun testGetSetComment() {
        Assertions.assertEquals("", column.comment)
        column.comment = "Comment"
        Assertions.assertEquals("Comment", column.comment)
        column.comment = "NewComment"
        Assertions.assertEquals("NewComment", column.comment)
    }

    @Test
    fun testToString() {
        column.comment = "Comment"
        Assertions.assertEquals("SpecificationColumn(cells: [1, 2, 3, 4, 5], comment: Comment)", column.toString())
    }
}