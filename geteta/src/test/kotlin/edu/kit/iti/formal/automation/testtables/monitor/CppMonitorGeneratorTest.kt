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
package edu.kit.iti.formal.automation.testtables.monitor

import com.google.common.truth.Truth
import edu.kit.iti.formal.automation.testtables.TableTester
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.getUsedGlobalVariables
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (25.10.19)
 */
internal class CppMonitorGeneratorTest : TableTester() {
    @Test
    fun testFindAssignment() {
        val table = getTable("monitor_binding")
        val tr = table.region.children.first() as TableRow

        val ga = table.constraintVariables.find { it.name == "ga" }
            ?.let { table.parseContext.getSMVVariable(it) }!!
        val gb = table.constraintVariables.find { it.name == "gb" }
            ?.let { table.parseContext.getSMVVariable(it) }!!

        val assignGa = (tr.inputExpr.values + tr.outputExpr.values).findAssignment(ga)
        val assignGb = (tr.inputExpr.values + tr.outputExpr.values).findAssignment(gb)

        Assertions.assertNotNull(assignGa)
        Assertions.assertNotNull(assignGb)

        Assertions.assertEquals("code\$CLK", assignGb!!.repr())
        Assertions.assertNotNull("code\$y", assignGa!!.repr())

        val sndRow = table.region.children[1] as TableRow
        val gvars = sndRow.getUsedGlobalVariables(table)
        println(gvars)
        Truth.assertThat(gvars).containsExactlyElementsIn(table.constraintVariables)
    }
}
