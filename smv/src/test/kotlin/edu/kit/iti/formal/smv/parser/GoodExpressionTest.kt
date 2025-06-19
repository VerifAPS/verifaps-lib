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
package edu.kit.iti.formal.smv.parser

import edu.kit.iti.formal.smv.ast.SMVExpr
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

object GoodExpressionTest {
    @ParameterizedTest
    @MethodSource("getGoodExpressions")
    fun testParser(testExpression: String) {
        val slp = TestHelper.getParser(testExpression)
        slp.expr()
        Assertions.assertEquals(0, slp.numberOfSyntaxErrors.toLong())
        // e.accept(SMVTransformToAST()) as SMVExpr
    }

    @ParameterizedTest
    @MethodSource("getGoodExpressions")
    fun testLexer(testExpression: String) {
        val lex = SMVLexer(CharStreams.fromString(testExpression))
        lex.allTokens.forEach { t ->
            System.out.format(
                "%6s: %-20s (%d,%d)%n",
                lex.vocabulary.getDisplayName(t.type),
                t.text,
                t.line,
                t.charPositionInLine,
            )
        }
    }

    @ParameterizedTest
    @MethodSource("getGoodExpressions")
    fun testPrinter(testExpression: String) {
        val slp1 = TestHelper.getParser(testExpression!!)
        val e1 = slp1.expr()
        val expr1 = e1.accept(SMVTransformToAST()) as SMVExpr
        val out1 = expr1.repr()
        println(out1)

        val slp2 = TestHelper.getParser(out1)
        val e2 = slp2.expr()
        val expr2 = e2.accept(SMVTransformToAST()) as SMVExpr
        val out2 = expr2.repr()
        /*  Assertions.assertEquals(
                  testExpression!!.replace("[() ]".toRegex(), ""),
                  out2.replace("[() ]".toRegex(), ""))*/
        Assertions.assertEquals(0, slp2.numberOfSyntaxErrors.toLong())
        Assertions.assertEquals(out1, out2)
    }

    @JvmStatic
    fun getGoodExpressions() = TestHelper.loadLines("goodexpr.txt", 1)
}
