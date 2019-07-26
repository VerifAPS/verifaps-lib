package edu.kit.iti.formal.automation

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

import edu.kit.iti.formal.automation.datatypes.IECString
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource
import org.junit.jupiter.params.provider.ValueSource

/**
 * Created by weigl on 15.12.16.
 */
object LiteralTokenTest {
    @ParameterizedTest(name="{0}")
    @ValueSource(strings = ["47474.759", "LWORD#2#11010", "0.456_262", "1.34E-12", "1e1",
        "1.34e1", "'abc$'abc'",
        "\"abc\$\"a\$n\$t\$rbc\"",
        "\"abc\$\"abc\"",
        "T#5d14h12m18s5ms", "T#5d_14h_12m_18s_5ms", "TIME#5d_14h_12m_5ms"])
    fun testTokens(expr: String) {
        val lexer = IEC61131Lexer(CharStreams.fromString(expr))
        val toks = lexer.allTokens
        println("$expr\t$toks")
        Assertions.assertEquals(1, toks.size.toLong())
    }


    @ParameterizedTest
    @CsvSource(value = ["abc$'abc,abc'abc", "a\$Ta,a\ta", "a\$Tb\$tc,a\tb\tc", "\$65,A"])
    fun interpretStrings(lit: String, exp: String): Unit {
        val v = IECString.interpret(lit, false)
        Assertions.assertEquals(exp, v)
    }
}
