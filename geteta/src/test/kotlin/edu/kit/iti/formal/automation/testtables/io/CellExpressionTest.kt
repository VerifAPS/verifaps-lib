/**
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
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
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ColumnCategory
import edu.kit.iti.formal.automation.testtables.model.ParseContext
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SVariable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * Created by weigl on 15.12.16.
 */
object CellExpressionTest {
    @TestFactory
    fun createExpressionTests(): List<DynamicTest> {
        return CASES.map { (a, b) ->
            DynamicTest.dynamicTest(a) { parse(a, b) }
        }
    }

    private val gtt: GeneralizedTestTable
    private val pc: ParseContext

    init {
        this.gtt = defaultTestTable()
        pc = gtt.parseContext
    }

    fun parse(expr: String, exp: String) {
        println("Test: $expr")
        val v = SVariable.create("Q").withSigned(16)
        val e = GetetaFacade.exprToSMV(expr, v, 0, pc)
        println(e.repr())
        Assertions.assertEquals(exp, e.repr());
    }

    internal fun defaultTestTable(run: Int = 0): GeneralizedTestTable {
        val gtt = GeneralizedTestTable()
        gtt.options.relational = true;
        gtt.add(iovar("a", "input", run))
        gtt.add(iovar("a", "input", 1))
        gtt.add(iovar("b", "input", run))
        gtt.add(iovar("c", "input", run))
        gtt.add(iovar("d", "input", run))
        gtt.add(iovar("Q", "output", 0))
        gtt.add(iovar("Q", "output", 1))
        gtt.ensureProgramRuns()
        return gtt
    }

    private fun iovar(name: String, io: String, run: Int) =
            ProgramVariable(name, INT, SMVTypes.signed(16),
                    if (io == "input") ColumnCategory.ASSUME else ColumnCategory.ASSERT,
                    programRun = run)

    val CASES = arrayOf(
            "|>" to "_1\$Q = Q",
            ">2" to "Q > 0sd16_2",
            "<52152343243214234" to "Q < 0sd16_52152343243214234",
            "!=6" to "Q != 0sd16_6",
            "<>-16134" to "Q != -0sd16_16134",
            "-243261" to "-0sd16_243261 = Q",
            "a" to "_0\$a = Q",
            "a+b" to "_0\$a + _0\$b",
            "(a)+(((b+c)+d))/2" to "_0\$a + (_0\$b + _0\$c + _0\$d) / 0sd16_2",
            "convert(a,2)" to "convert(_0\$a, 0sd16_2)",
            "TRUE" to "TRUE = Q",
            "true" to "TRUE = Q",
            "false" to "FALSE = Q",
            "FALSE" to "FALSE = Q",
            "a[-5]" to "_0\$a__history._\$5 = Q",
            "[2+2, 6]" to "0sd16_2 + 0sd16_2 <= Q & Q <= 0sd16_6",
            "[-61+2, -61]" to "-0sd16_61 + 0sd16_2 <= Q & Q <= -0sd16_61",
            "0|>a" to "_0\$a = Q",
            "|>a" to "_1\$a = Q",
            "0::a + |>a" to "_0\$a + _1\$a",
            "·" to "_1\$Q = Q"
    )
}
