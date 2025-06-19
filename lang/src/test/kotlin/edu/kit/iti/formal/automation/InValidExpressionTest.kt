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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

/**
 * @author Alexander Weigl
 * @version 1 (02.08.16)
 */
object InValidExpressionTest {

    @ParameterizedTest
    @MethodSource("getExpressions")
    fun testInValidExpression(invalid: String) {
        val parser = IEC61131Facade.getParser(CharStreams.fromString(invalid))
        var error = try {
            val ctx = parser.expression()
            println(ctx.toString(parser))
            println(IEC61131Facade.print(IEC61131Facade.expr(invalid)))
            println(ctx.stop.tokenSource.nextToken())
            ctx.stop.tokenSource.nextToken().text != "EOF"
            // error = false;
        } catch (e: Exception) {
            true
        }

        error = error || parser.numberOfSyntaxErrors > 0
        println(parser.numberOfSyntaxErrors)
        assertTrue(error)
    }

    @JvmStatic
    fun getExpressions() = TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/invalid.txt")
}
