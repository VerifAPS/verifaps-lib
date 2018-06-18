package edu.kit.iti.formal.automation.st

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.TestUtils
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import org.antlr.v4.runtime.ANTLRInputStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.Token
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

/**
 * Created by weigl on 15.12.16.
 */
@RunWith(Parameterized::class)
class LiteralTokenTest {

    @Parameterized.Parameter(0)
    var expr: String? = null

    @Test
    fun testTokens() {
        val lexer = IEC61131Lexer(ANTLRInputStream(expr!!))
        val toks = lexer.allTokens
        println(toks)
        Assert.assertEquals(1, toks.size.toLong())
    }

    companion object {
        internal var CASES = arrayOf(
                //"LWORD#2#22020",
                "47474.759", "LWORD#2#11010", "0.456_262", "1.34E-12", "1e1", "1.34e1", "T#5d14h12m18s5ms", "T#5d_14h_12m_18s_5ms", "TIME#5d_14h_12m_5ms")

        @Parameterized.Parameters(name = "{0}")
        fun data(): Collection<Array<Any>> {
            return TestUtils.asParameters(CASES)
        }
    }
}
