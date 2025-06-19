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
package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

class TestTypeChecker {
    private val varTypeCtx = mapOf("X" to TypeInt)
    private val checker = TypeChecker(varTypeCtx)

    @Test
    @Throws(TypeCheckException::class)
    fun testValidType() {
        // Colors = Red, Blue
        // Red == Blue && X == 3 && 5 + X == 8 && TRUE

        val colorsEnum = enumOfName("Colors", "Red", "Blue")

        val redEqualsBlue =
            SimpleExpressions.equal(
                SimpleExpressions.literal(colorsEnum.valueOf("Red")),
                SimpleExpressions.literal(colorsEnum.valueOf("Blue")),
            )

        val xEqualsThree =
            SimpleExpressions.equal(
                SimpleExpressions.variable("X"),
                SimpleExpressions.literal(3),
            )

        val sumIsEleven =
            SimpleExpressions.equal(
                SimpleExpressions.plus(SimpleExpressions.literal(5), SimpleExpressions.variable("X")),
                SimpleExpressions.literal(8),
            )

        val trueExpr = SimpleExpressions.literal(true)

        val validExpression =
            SimpleExpressions.and(
                redEqualsBlue,
                SimpleExpressions.and(xEqualsThree, SimpleExpressions.and(sumIsEleven, trueExpr)),
            )

        val type = checker.typeCheck(validExpression)
        Assertions.assertEquals(type, TypeBool)
    }

    @Test // (expected = TypeCheckException::class)
    @Throws(TypeCheckException::class)
    fun testInvalidArgumentType() {
        val invalidExpression =
            SimpleExpressions.and(SimpleExpressions.literal(false), SimpleExpressions.literal(2))
        assertFailsWith<TypeCheckException> {
            checker.typeCheck(invalidExpression)
        }
    }
}