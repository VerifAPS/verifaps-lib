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
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.IoVariable
import edu.kit.iti.formal.automation.testtables.model.IoVariableType
import edu.kit.iti.formal.smv.ast.SVariable
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

/**
 * Created by weigl on 15.12.16.
 */
@RunWith(Parameterized::class)
class CellExpressionTest(private var expr: String) {
    private val gtt: GeneralizedTestTable

    init {
        this.gtt = defaultTestTable()
    }

    @Test
    fun parse() {
        val v = SVariable.create("Q").withSigned(16)
        val e = IOFacade.parseCellExpression(expr, v, gtt)
        println(e)
    }

    companion object {
        internal fun defaultTestTable(): GeneralizedTestTable {
            val gtt = GeneralizedTestTable()
            gtt.add(iovar("a", "input"))
            gtt.add(iovar("b", "input"))
            gtt.add(iovar("c", "input"))
            gtt.add(iovar("d", "input"))
            return gtt
        }

        private fun iovar(name: String, io: String) =
                IoVariable(name, INT,
                        if (io == "input") IoVariableType.INPUT else IoVariableType.OUTPUT)

        val CASES = arrayOf(">2", "<52152343243214234", "!=6", "<>-16134", "-243261", "a", "a+b", "(a)+(((b+c)+d))/2", "convert(a,2)", "TRUE", "true", "false", "FALSE", "a[-5]", "[2+2, 6]", "[-61+2, -61]")
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun genTests(): List<Array<Any>> {
            return CASES.map { s -> arrayOf<Any>(s) }
        }
    }
}
