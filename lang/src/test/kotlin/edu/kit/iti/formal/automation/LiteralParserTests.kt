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
        assertEquals(
            TimeofDayData(20, 61, 0, 0),
            TimeofDayData.parse("20:61"),
        )

        assertEquals(
            TimeofDayData(20, 61, 10, 0),
            TimeofDayData.parse("20:61:10"),
        )

        assertEquals(
            TimeofDayData(20, 61, 62, 1005),
            TimeofDayData.parse("20:61:62.1005"),
        )
    }
}