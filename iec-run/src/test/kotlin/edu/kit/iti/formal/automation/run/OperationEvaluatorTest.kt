/*-
 * #%L
 * iec-run
 * %%
 * Copyright (C) 2018 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */
package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.datatypes.values.Values
import org.junit.Test

import org.junit.Assert.*
import java.math.BigInteger

class OperationEvaluatorTest {
    @Test
    fun add() {
        val a = AnyInt.getDataTypeFor(1024, false)
        val res = OperationEvaluator.add(Values.VAnyInt(a, BigInteger.valueOf(-19)), Values.VAnyInt(a, BigInteger.valueOf(2)))
        assertEquals(BigInteger.valueOf(-17), res.value)
    }

    @Test
    fun normalizeIntTest() {
        val a = AnyInt.getDataTypeFor(7, false)
        val b = AnyInt.getDataTypeFor(15, false)
        val c = AnyInt.getDataTypeFor(15, true)

        println("using type ${a} with lowerBound ${a.lowerBound} and upperBound ${a.upperBound}")
        println("using type ${b} with lowerBound ${b.lowerBound} and upperBound ${b.upperBound}")
        assertEquals(
                Values.VAnyInt(a, BigInteger.valueOf(-4)),
                OperationEvaluator.normalizeInt(Values.VAnyInt(a, BigInteger.valueOf(4))))
        assertEquals(
                Values.VAnyInt(b, BigInteger.valueOf(-8)),
                OperationEvaluator.normalizeInt(Values.VAnyInt(b, BigInteger.valueOf(8)))
        )
    }

}
