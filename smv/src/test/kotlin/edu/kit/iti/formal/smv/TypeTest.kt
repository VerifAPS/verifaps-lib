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
package edu.kit.iti.formal.smv

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (15.12.16)
 */
class TypeTest {
    @Test
    fun testOutput() {
        val u10 = SMVWordType(false, 10)
        val s0 = SMVWordType(true, 0)
        val b = SMVTypes.BOOLEAN
        val e = EnumType(Arrays.asList("a", "b", "c"))

        Assertions.assertEquals("unsigned word[10]", u10.repr())
        Assertions.assertEquals("boolean", b.repr())
        Assertions.assertEquals("signed word[0]", s0.repr())
        Assertions.assertEquals("{a, b, c}", e.repr())
    }
}