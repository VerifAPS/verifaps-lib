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

import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.problems.CellTypeProblem.Companion.tryTypeCheckCellExpression
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class CellTypeProblemTest {
    private var typeCheckEx: TypeCheckException? = null
    private var problem: CellTypeProblem? = null

    @BeforeEach
    fun setUp() {
        typeCheckEx = TypeCheckException(
            BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, LiteralExpr(ValueInt(2)), LiteralExpr(ValueBool.TRUE)),
            "Expected type \"BOOL\"," +
                "but got \"INT\"",
        )
        problem = CellTypeProblem(typeCheckEx!!, "A", 4)
    }

    @Test
    @Throws(Exception::class)
    fun tryTypeCheckCellExpression() {
        val typeMap = mapOf("A" to TypeInt, "B" to TypeBool)
        val typeChecker = TypeChecker(typeMap)
        val problematicCell = SimpleExpressions.and(SimpleExpressions.literal(2), SimpleExpressions.literal(true))
        try {
            tryTypeCheckCellExpression(
                typeChecker,
                "A",
                4,
                problematicCell,
            )
        } catch (exc: SpecProblemException) {
            Assertions.assertEquals(problem, exc.problem)
        }
    }

    @Test
    fun typeCheckException() {
        Assertions.assertEquals(typeCheckEx, problem!!.exception)
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical = CellTypeProblem(typeCheckEx!!, "A", 4)
        Assertions.assertEquals(problem, identical)
        Assertions.assertNotEquals(problem, null)
        Assertions.assertEquals(problem, problem)
        val notIdentical = CellTypeProblem(typeCheckEx!!, "A", 5)
        Assertions.assertNotEquals(notIdentical, problem)
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        val identical = CellTypeProblem(typeCheckEx!!, "A", 4)
        Assertions.assertEquals(problem.hashCode().toLong(), identical.hashCode().toLong())
        Assertions.assertEquals(problem.hashCode().toLong(), problem.hashCode().toLong())
        val notIdentical = CellTypeProblem(typeCheckEx!!, "A", 5)
        Assertions.assertNotEquals(notIdentical.hashCode().toLong(), problem.hashCode().toLong())
    }
}