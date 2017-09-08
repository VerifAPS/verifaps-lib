/*-
 * #%L
 * iec-run
 * %%
 * Copyright (C) 2017 Alexander Weigl
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */
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
