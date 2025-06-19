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

import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.table.ConstraintCell
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by bal on 26.02.17.
 */
class CellParseProblemTest {
    private var parseEx =
        ParseException(1, 2, "extraneous input '<>' expecting {'(', '-', NOT, 'if', T, F, IDENTIFIER, INTEGER}")
    private var problem = CellParseProblem(parseEx, "A", 4)

    @Test
    fun expressionOrProblemForCell() {
        val typeContext = listOf(TypeInt, TypeBool)
        val typeMap: MutableMap<String, Type> = HashMap()
        typeMap["A"] = TypeInt
        typeMap["B"] = TypeBool
        val typeChecker = TypeChecker(typeMap)
        val problematicCell = ConstraintCell("3<<>4")
        assertFailsWith<SpecProblemException> {
            ConstraintSpecificationValidator.tryValidateCellExpression(
                typeContext,
                typeChecker,
                "A",
                4,
                problematicCell,
            )
        }
    }

    @Test
    fun testEquals() {
        val identical = CellParseProblem(parseEx, "A", 4)
        Assertions.assertEquals(problem, identical)
        Assertions.assertNotEquals(problem, null)
        Assertions.assertEquals(problem, problem)
        Assertions.assertNotEquals(CellParseProblem(parseEx, "B", 4), problem)
    }

    @Test
    fun testHashCode() {
        val identical = CellParseProblem(parseEx, "A", 4)
        Assertions.assertEquals(problem.hashCode().toLong(), identical.hashCode().toLong())
        Assertions.assertEquals(problem.hashCode().toLong(), problem.hashCode().toLong())
        Assertions.assertNotEquals(CellParseProblem(parseEx, "B", 4).hashCode().toLong(), problem.hashCode().toLong())
    }

    @Test
    fun parseException() {
        Assertions.assertEquals(parseEx, problem.parseException)
    }
}