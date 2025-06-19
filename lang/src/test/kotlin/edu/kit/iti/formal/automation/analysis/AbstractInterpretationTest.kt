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
package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import org.antlr.v4.runtime.misc.IntervalSet
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource

/**
 * @author Alexander Weigl
 * @version 1 (07.11.19)
 */
internal class AbstractInterpretationTest {
    lateinit var ai: AbstractInterpretation<IntervalSet>
    lateinit var start: AState<IntervalSet>

    @BeforeEach
    fun setup() {
        start = AState()
        start["a"] = IntervalSet(1, 2, 3, 4, 5)
        start["b"] = IntervalSet(10, 11)
        start["c"] = IntervalSet(-5, -2)

        start["t"] = IntervalSet(1)
        start["f"] = IntervalSet(0)
        start["u"] = IntervalSet(0, 1)

        ai = AbstractInterpretation(IntLattice(), start)
    }

    @ParameterizedTest(name = "{0}")
    @CsvSource(
        delimiter = ';',
        value = [
            "b;         10,11",
            "c;         -2,-5",
            "a+b+c;     6..14",
            "b*c;       -55..-50,-22..-20",
            "t and f;   0",
            "u and f;   0",
            "t or u;    1",
            "t and u;   0,1",
            "a+3;       4,5,6,7,8",
            "3/2;       1,2",
            "10/2;      5",
            "2+3;       5",
            "2+3*4;     14",
            "10/1;      10",
            "true AND false OR false; 0",
        ],
    )
    fun testVariablesAndExpr(expr: String, exp: String) {
        println("Expr: $expr")
        val a = ai.interpret(IEC61131Facade.expr(expr))
        val set = IntervalSet()
        exp.split(",").forEach {
            if (".." in it) {
                val (a, b) = it.split("..", limit = 2)
                set.add(a.toInt(), b.toInt())
            } else {
                set.add(it.toInt())
            }
        }
        Assertions.assertEquals(set, a)
    }

    @Test
    fun testIf() {
        val stmt = IEC61131Facade.statements(
            """
            IF u THEN 
                q := 20;
            ELSEIF f THEN //always false
                q := -20;
            ELSEIF t or u THEN
                q := 10;
            END_IF; 
            q := q + c;
            """.trimIndent(),
        )
        val result = ai.interpret(stmt)
        println(result["q"])
    }

    @Test
    fun testFor() {
        val stmt = IEC61131Facade.statements(
            """
            q := 0;
            for i := 0 to 5 do
                q := q + i; 
            END_FOR 
            """.trimIndent(),
        )
        val result = ai.interpret(stmt)
        println(result["q"])
        Assertions.assertEquals(IntervalSet(15), result["q"])
    }

    @Test
    fun testWhileFixpoint() {
        val stmt = IEC61131Facade.statements(
            """
            q := 0;
            while TRUE do
                q := 1;
            end_while
            """.trimIndent(),
        )
        val result = ai.interpret(stmt)
        println(result["q"])
        Assertions.assertEquals(IntervalSet.of(1), result["q"])
    }
}
