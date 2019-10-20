package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.TableTester
import edu.kit.iti.formal.automation.testtables.apps.Geteta
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
        checkDefinition(b, "A_out_Sum", "0sd16_0 = Sum_0");
        checkDefinition(b,  "A_out_Equal", "TRUE");


        checkDefinition(b, "Equal_0", "code\$x");
        checkDefinition(b, "Equal_1", "code\$y");
        checkDefinition(b, "B_out_Equal", "Equal_0 = Equal_1");

        checkDefinition(b, "C_out_Equal", "Equal_0 <= Equal_1");


        println(b.tableModule.repr())
    }

    private fun checkDefinition(b: SMVConstructionModel, name: String, expected: String) {
        val modelDefinition = b.tableModule.definitions.find { it.target.name == name }
        Assertions.assertNotNull(modelDefinition, "Defintion '$name' not found.")
        Assertions.assertEquals(expected, modelDefinition!!.expr.repr())
    }
}