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
package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.logic.specification.smtlib.BitvectorUtils.hexFromInt
import edu.kit.iti.formal.stvs.logic.specification.smtlib.BitvectorUtils.intFromHex
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by leonk on 21.02.2017.
 */
class BitvectorUtilsTest {
    @Test
    fun testEquality() {
        for (i in -32768..32767) {
            Assertions.assertEquals(i.toLong(), intFromHex(hexFromInt(i, 4).toString(), true).toLong())
        }
        for (i in 0..65535) {
            Assertions.assertEquals(i.toLong(), intFromHex(hexFromInt(i, 4).toString(), false).toLong())
        }
    }

    @Test
    fun testCritical() {
        Assertions.assertEquals(32767, intFromHex("#x7FFF", true).toLong())
        Assertions.assertEquals(-32768, intFromHex("#x8000", true).toLong())
        Assertions.assertEquals(0, intFromHex("#x0000", true).toLong())
        Assertions.assertEquals(-1, intFromHex("#xFFFF", true).toLong())

        Assertions.assertEquals(32767, intFromHex("#x7FFF", false).toLong())
        Assertions.assertEquals(32768, intFromHex("#x8000", false).toLong())
        Assertions.assertEquals(0, intFromHex("#x0000", false).toLong())
        Assertions.assertEquals(65535, intFromHex("#xFFFF", false).toLong())
    }

    @Test
    fun testWrongFormat() {
        assertFailsWith<IllegalArgumentException> { intFromHex("notvalid", true) }
    }
}