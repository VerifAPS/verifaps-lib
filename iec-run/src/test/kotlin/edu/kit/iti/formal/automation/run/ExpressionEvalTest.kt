package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.BufferedReader
import java.io.InputStreamReader
import java.util.*

/**
 * @author Alexander Weigl
 * *
 * @version 1 (23.06.17)
 */
@RunWith(Parameterized::class)
class ExpressionEvalTest(val expr: String, val expected: String) {
    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        public fun read(): Iterable<Array<Any>> {
            val r = ExpressionEvalTest::class.java.getResourceAsStream("evaluation.txt")
            if (r !== null) {
                val list = ArrayList<Array<Any>>()
                val reader = BufferedReader(InputStreamReader(r))
                for (line in reader.lineSequence()) {
                    list.add(line.split(">>>").toTypedArray())
                }
                return list
            } else {
                println("Could  not load evaluation.txt")
                return ArrayList()
            }
        }
    }


    @Test
    public fun eval() {
        val state = State()
        val ee = ExpressionEval.create(state)
        val e = IEC61131Facade.expr(expr)
        val f = IEC61131Facade.expr(expected)
        val got = ee.eval(e)
        val exp = ee.eval(f)
        Assert.assertEquals(exp, got)
    }

}