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

import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser.Companion.parse
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by philipp on 23.01.17.
 */
class TestIntervalParser {
    @Test
    fun testWildcard() {
        assertParseEqual("-", " as [0,-]", 0, null)
    }

    @Test
    fun testUpperBoundWildcard() {
        assertParseEqual("[5,-]", "", 5, null)
    }

    @Test
    fun testSimpleInterval() {
        assertParseEqual("[1,3]", "", 1, 3)
    }

    @Test
    fun testConstant() {
        assertParseEqual("3", " as [3,3]", 3, 3)
    }

    @Test // (expected = ParseException::class)
    fun testNotNumbersInInterval() {
        assertFailsWith<IllegalStateException> {
            parse("[a,b]")
        }
    }

    @Test // (expected = ParseException::class)
    fun testLowerBoundHigherThanHigherBound() {
        assertFailsWith<IllegalArgumentException> {
            parse("[3,2]")
        }
    }

    @Test // (expected = ParseException::class)
    fun testNoNegativeNumbersAllowedInConstant() {
        // assertFailsWith<IllegalArgumentException> {
        parse("-1")
        // }
    }

    @Test // (expected = ParseException::class)
    fun testNoNegativeNumbersAllowedInInterval() {
        assertFailsWith<SyntaxErrorReporter.ParserException> {
            parse("[-3,-1]")
        }
    }

    companion object {
        private fun assertParseEqual(toBeParsed: String, elaborationText: String, lower: Int, upper: Int?) {
            Assertions.assertEquals(
                LowerBoundedInterval(lower, upper),
                parse(toBeParsed),
                "Parse $toBeParsed$elaborationText",
            )
        }
    }
}