package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.datatypes.values.TimeofDayData
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
class LiteralParserTests {
    @Test
    fun parseTimeOfDayLiteralErrorHour() {
        assertThrows<IllegalArgumentException> {
            TimeofDayData.parse("200:61")
        }
    }

    @Test
    @Throws(Exception::class)
    fun parseTimeOfDayLiteralErrorMin() {
        assertThrows<IllegalArgumentException> {
            TimeofDayData.parse("20:610:20")
        }
    }

    @Test
    fun parseTimeOfDayLiteralErrorSec() {
        assertThrows<IllegalArgumentException> {
            TimeofDayData.parse("20:61:a")
        }
    }

    @Test
    fun parseTimeOfDayLiteralErrorMsec() {
        assertThrows<IllegalArgumentException> {
            TimeofDayData.parse("200:61:1.6a")
        }
    }

    @Test
    fun parseTimeOfDayLiteral1() {
        assertEquals(TimeofDayData(20, 61, 0, 0),
                TimeofDayData.parse("20:61"))

        assertEquals(TimeofDayData(20, 61, 10, 0),
                TimeofDayData.parse("20:61:10"))

        assertEquals(TimeofDayData(20, 61, 62, 1005),
                TimeofDayData.parse("20:61:62.1005"))
    }
}
