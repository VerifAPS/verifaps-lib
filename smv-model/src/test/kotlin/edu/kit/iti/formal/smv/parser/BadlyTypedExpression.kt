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
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (01.05.17)
 */
@RunWith(Parameterized::class)
class BadlyTypedExpression {

    @Parameterized.Parameter
    var testExpression: String? = null

    @Test
    fun test() {
        val slp = TestHelper.getParser(testExpression!!)
        val e = slp.expr()
        Assert.assertEquals(0, slp.numberOfSyntaxErrors.toLong())
        val expr = e.accept(SMVTransformToAST()) as SMVExpr
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        @Throws(IOException::class)
        fun getBadExpressions() = TestHelper.loadLines("badlytypedexpr.txt", 1)
    }
}
