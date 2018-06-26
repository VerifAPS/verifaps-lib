package edu.kit.iti.formal.smv.parser

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.smv.ast.SMVExpr
import org.antlr.v4.runtime.CharStreams
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

import java.io.IOException

@RunWith(Parameterized::class)
class GoodExpressionTest(var testExpression: String) {
    @Test
    @Throws(IOException::class)
    fun testParser() {
        val slp = TestHelper.getParser(testExpression!!)
        val e = slp.expr()
        Assert.assertEquals(0, slp.numberOfSyntaxErrors.toLong())
        val expr = e.accept(SMVTransformToAST()) as SMVExpr
        // TODO
        //String out = expr.accept(new StringPrinter());
        //System.out.println(">>> " + out);
    }

    @Test
    fun testLexer() {
        val lex = SMVLexer(CharStreams.fromString(testExpression!!))
        lex.allTokens.forEach { t ->
            System.out.format("%6s: %-20s (%d,%d)%n",
                    lex.vocabulary.getDisplayName(t.type),
                    t.text,
                    t.line,
                    t.charPositionInLine)
        }
    }

    @Test
    fun testPrinter() {
        val slp1 = TestHelper.getParser(testExpression!!)
        val e1 = slp1.expr()
        val expr1 = e1.accept(SMVTransformToAST()) as SMVExpr
        val out1 = expr1.repr()
        println(out1)


        val slp2 = TestHelper.getParser(out1)
        val e2 = slp2.expr()
        val expr2 = e2.accept(SMVTransformToAST()) as SMVExpr
        val out2 = expr2.repr()
      /*  Assert.assertEquals(
                testExpression!!.replace("[() ]".toRegex(), ""),
                out2.replace("[() ]".toRegex(), ""))*/
        Assert.assertEquals(0, slp2.numberOfSyntaxErrors.toLong())
        Assert.assertEquals(out1, out2)
    }

    companion object {

        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        @Throws(IOException::class)
        fun getGoodExpressions() = TestHelper.loadLines("goodexpr.txt", 1)
    }
}
