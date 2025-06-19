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
import edu.kit.iti.formal.smt.SmtFacade
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * @author Alexander Weigl
 * @version 1 (13.10.18)
 */
class SmtFacadeTest {
    @TestFactory
    fun intFromHex1Byte(): Collection<DynamicTest> {
        val testcases = (0..255).map {
            it.toBigDecimal() to String.format("#x%02X", it)
        }
        return testcases.map { (a, b) ->
            DynamicTest.dynamicTest(b) {
                val r = SmtFacade.hexFromInt(a.toBigInteger(), 8)
                Assertions.assertEquals(b, r)
            }
        }
    }

    @TestFactory
    fun intFromHex1ByteNeg(): Collection<DynamicTest> {
        val testcases = ((-1).downTo(-128)).map {
            it.toBigDecimal() to String.format("#x%02X", 256 + it)
        }
        return testcases.map { (a, b) ->
            DynamicTest.dynamicTest(b) {
                val r = SmtFacade.hexFromInt(a.toBigInteger(), 8)
                Assertions.assertEquals(b, r)
            }
        }
    }

    @TestFactory
    fun testIntToHex4Bytes(): List<DynamicTest> {
        val testcases = arrayOf(
            32767 to "#x7FFF",
            -32768 to "#x8000",
            0 to "#x0000",
            -1 to "#xFFFF",
            32768 to "#x8000",
            65535 to "#xFFFF",
        )
        return testcases.map { (a, b) ->
            DynamicTest.dynamicTest(b) {
                val r = SmtFacade.hexFromInt(a.toBigInteger(), 2 * 8)
                Assertions.assertEquals(b, r)
            }
        }
    }

    /*
    @Test
    fun testReverse() {
        for (i in -32768..32767) {
            assertEquals(i, BitvectorUtils.intFromHex(BitvectorUtils.hexFromInt(i, 4), true))
        }
        for (i in 0..65535) {
            assertEquals(i, BitvectorUtils.intFromHex(BitvectorUtils.hexFromInt(i, 4), false))
        }
    }*/
}