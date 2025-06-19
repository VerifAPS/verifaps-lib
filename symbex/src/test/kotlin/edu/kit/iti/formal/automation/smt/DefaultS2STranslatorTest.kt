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
package edu.kit.iti.formal.automation.smt

import edu.kit.iti.formal.automation.smt.DefaultS2STranslator.Companion
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.math.BigInteger

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
class DefaultS2STranslatorTest {
    @Test
    @Throws(Exception::class)
    fun testPaddedString() {
        assertEquals(
            "             abc",
            String(Companion.paddedString(16, ' ', "abc")),
        )

        assertEquals(
            "00001111",
            String(Companion.paddedString(8, '0', "1111")),
        )

        assertEquals(
            "1111",
            String(Companion.paddedString(0, '0', "1111")),
        )
    }

    @Test
    @Throws(Exception::class)
    fun testTwoComplement() {
        assertEquals(
            "00000001",
            Companion.twoComplement(BigInteger.ONE, 8),
        )
        assertEquals(
            "11111111",
            Companion.twoComplement(BigInteger.ONE.negate(), 8),
        )
    }
}
