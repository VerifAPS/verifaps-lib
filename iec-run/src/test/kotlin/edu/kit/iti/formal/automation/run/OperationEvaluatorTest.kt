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