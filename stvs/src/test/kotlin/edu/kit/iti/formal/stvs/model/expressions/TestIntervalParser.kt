package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser.Companion.parse
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.util.*

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

    @Test//(expected = ParseException::class)
    fun testNotNumbersInInterval() {
        parse("[a,b]")
    }

    @Test//(expected = ParseException::class)

    fun testLowerBoundHigherThanHigherBound() {
        parse("[3,2]")
    }

    @Test//(expected = ParseException::class)
    fun testNoNegativeNumbersAllowedInConstant() {
        parse("-1")
    }

    @Test//(expected = ParseException::class)
    fun testNoNegativeNumbersAllowedInInterval() {
        parse("[-3,-1]")
    }

    companion object {
        private fun assertParseEqual(toBeParsed: String, elaborationText: String, lower: Int, upper: Int?) {
            Assertions.assertEquals(
                LowerBoundedInterval(lower, Optional.ofNullable(upper)),
                parse(toBeParsed),
                "Parse $toBeParsed$elaborationText"
            )
        }
    }
}
