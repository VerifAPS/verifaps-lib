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
package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class CellUnsupportedExpressionProblemTest {
    private var problem: CellUnsupportedExpressionProblem? = null
    private var unsupportedExpressionEx: UnsupportedExpressionException? = null

    @BeforeEach
    @Throws(Exception::class)
    fun setUp() {
        unsupportedExpressionEx = UnsupportedExpressionException("ExpressionText")
        problem = CellUnsupportedExpressionProblem(unsupportedExpressionEx!!, "A", 4)
    }

    @Test
    fun unsupportedExpression() {
        Assertions.assertEquals(unsupportedExpressionEx, problem!!.exception)
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!,
            "A",
            4,
        )
        Assertions.assertEquals(identical, problem)
        Assertions.assertNotEquals(null, problem)
        Assertions.assertEquals(problem, problem)
        val notIdentical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!,
            "A",
            5,
        )
        Assertions.assertNotEquals(notIdentical, problem)
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        val identical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!,
            "A",
            4,
        )
        Assertions.assertEquals(identical.hashCode().toLong(), problem.hashCode().toLong())
        Assertions.assertEquals(problem.hashCode().toLong(), problem.hashCode().toLong())
        val notIdentical = CellUnsupportedExpressionProblem(
            unsupportedExpressionEx!!,
            "A",
            5,
        )
        Assertions.assertNotEquals(notIdentical.hashCode().toLong(), problem.hashCode().toLong())
    }
}