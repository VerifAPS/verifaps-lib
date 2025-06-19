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
package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.TableTester
import edu.kit.iti.formal.automation.testtables.builder.SMVConstructionModel
import edu.kit.iti.formal.smv.EnumType
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 *
 * @author Alexander Weigl
 * @version 1 (18.10.19)
 */
class ProjectionVariableTest : TableTester() {
    @Test
    fun test() {
        val columnsTable = getTable("columns")
        val a = GetetaFacade.constructTable(columnsTable)
        val b = GetetaFacade.constructSMV(a, EnumType(listOf()))

        checkDefinition(b, "Sum_0", "code\$x + code\$y")
        checkDefinition(b, "A_out_Sum", "0sd16_0 = Sum_0")
        checkDefinition(b, "A_out_Equal", "TRUE")

        checkDefinition(b, "Equal_0", "code\$x")
        checkDefinition(b, "Equal_1", "code\$y")
        checkDefinition(b, "B_out_Equal", "Equal_0 = Equal_1")

        checkDefinition(b, "C_out_Equal", "Equal_0 <= Equal_1")

        println(b.tableModule.repr())
    }

    private fun checkDefinition(b: SMVConstructionModel, name: String, expected: String) {
        val modelDefinition = b.tableModule.definitions.find { it.target.name == name }
        Assertions.assertNotNull(modelDefinition, "Defintion '$name' not found.")
        Assertions.assertEquals(expected, modelDefinition!!.expr.repr())
    }
}
