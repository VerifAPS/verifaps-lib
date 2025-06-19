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
package edu.kit.iti.formal.automation

import TestUtils
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

/**
 * Created by weigl on 02.08.16.
 */
object ValidExpressionTest {
    @ParameterizedTest(name = "{0}")
    @MethodSource("getExpressions")
    fun testValidExpression(validExpression: String) {
        assertTrue(test(validExpression))
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("getExpressions")
    fun testCopy(validExpression: String) {
        val e = IEC61131Facade.expr(validExpression)
        Assertions.assertEquals(e, e.clone())
    }

    @JvmStatic
    fun getExpressions() = TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/valid.txt")

    internal fun test(s: String?): Boolean {
        val parser = IEC61131Facade.getParser(CharStreams.fromString(s!!))
        try {
            val ctx = parser.expression()
            println(ctx.toString(parser))
            assertEquals(
                "<EOF>",
                ctx.stop.tokenSource.nextToken().text,
                "input was not completely consumed",
            )
        } catch (e: Exception) {
            e.printStackTrace()
            return false
        }

        return parser.numberOfSyntaxErrors == 0
    }
}
