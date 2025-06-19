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
package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.math.BigInteger

class OperationEvaluatorTest {
    @Test
    fun add() {
        val a = AnyInt.getDataTypeFor(1024, false)
        val res = OperationEvaluator.add(
            VAnyInt(a, BigInteger.valueOf(-19)),
            VAnyInt(a, BigInteger.valueOf(2)),
        )
        assertEquals(BigInteger.valueOf(-17), res.value)
    }

    @Test
    fun normalizeIntTest() {
        assertEquals(
            VAnyInt(INT, BigInteger.valueOf(4)),
            OperationEvaluator.normalizeInt(VAnyInt(INT, 4)),
        )
        assertEquals(
            VAnyInt(UINT, 8),
            OperationEvaluator.normalizeInt(VAnyInt(UINT, -8)),
        )
    }
}
