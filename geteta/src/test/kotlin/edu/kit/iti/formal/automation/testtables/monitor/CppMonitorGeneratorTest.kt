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