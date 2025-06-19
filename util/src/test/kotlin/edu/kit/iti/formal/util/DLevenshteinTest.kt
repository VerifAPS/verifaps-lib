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
package edu.kit.iti.formal.util

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * @author Alexander Weigl
 * @version 1 (03.02.19)
 */
class DLevenshteinTest {
    @TestFactory
    fun dlevenshtein(): Collection<DynamicTest> = listOf(
        dlevenshteinTest("", "", 0),
        dlevenshteinTest("ac", "ac", 0),
        dlevenshteinTest("abc", "aXc", 1),
        dlevenshteinTest("abc", "bac", 1),
        dlevenshteinTest("abc", "", 3),
        dlevenshteinTest("abc", "cba", 2),
    )

    private fun dlevenshteinTest(source: String, target: String, expCost: Int) = DynamicTest.dynamicTest("$source/$target/$expCost", { doTest(source, target, expCost) })

    private fun doTest(source: String, target: String, expCost: Int) {
        assertEquals(expCost, dlevenshtein(source, target))
    }
}
