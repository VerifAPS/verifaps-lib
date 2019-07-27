package edu.kit.iti.formal.automation.testtables

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.TestInstance
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (27.07.19)
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
open class TableTester {
    var gtts = ArrayList<GeneralizedTestTable>()

    @BeforeAll
    fun setUp() {
        gtts.addAll(GetetaFacade.parseTableDSL(
                File("src/test/resources/tables.tt")))
        Assertions.assertTrue(gtts.isNotEmpty())
    }

    fun getTable(s: String): GeneralizedTestTable {
        val t = gtts.find { it.name == s }
        Assertions.assertNotNull(t)
        return t!!
    }
}