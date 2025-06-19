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
package edu.kit.iti.formal.automation.datatypes

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (04.02.19)
 */
class DataTypeAssignabilityTest {
    @Test
    fun visitIntegers() {
        assertTrue(INT.isAssignableTo(DINT))
        assertTrue(INT.isAssignableTo(INT))
        assertTrue(INT.isAssignableTo(LINT))
        assertTrue(SINT.isAssignableTo(DINT))
        assertTrue(SINT.isAssignableTo(INT))
        assertTrue(SINT.isAssignableTo(LINT))
        assertTrue(SINT.isAssignableTo(SINT))
        assertTrue(DINT.isAssignableTo(DINT))
        assertTrue(DINT.isAssignableTo(LINT))
        assertTrue(LINT.isAssignableTo(LINT))

        assertFalse(INT.isAssignableTo(SINT))
        assertFalse(DINT.isAssignableTo(SINT))
        assertFalse(DINT.isAssignableTo(INT))
        assertFalse(LINT.isAssignableTo(SINT))
        assertFalse(LINT.isAssignableTo(DINT))
        assertFalse(LINT.isAssignableTo(INT))
    }

    @Test
    fun visitBits() {
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.BOOL))
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.DWORD))
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.LWORD))
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.WORD))
        assertFalse(AnyBit.BOOL.isAssignableTo(INT))
        assertFalse(AnyBit.BOOL.isAssignableTo(SINT))
    }

    @Test
    fun visit2() {
    }

    @Test
    fun visit3() {
    }

    @Test
    fun visit4() {
    }

    @Test
    fun visit5() {
    }

    @Test
    fun visit6() {
    }

    @Test
    fun visit7() {
    }

    @Test
    fun visit8() {
    }

    @Test
    fun visit9() {
    }

    @Test
    fun visit10() {
    }
}