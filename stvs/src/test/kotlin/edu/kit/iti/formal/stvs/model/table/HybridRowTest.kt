package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import org.junit.jupiter.api.Assertions

import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.*

/**
 * Created by bal on 25.02.17.
 */
class HybridRowTest {
    private var hybridRow: HybridRow? = null
    private var constraintSpec: ConstraintSpecification? = null

    @BeforeEach
    @Throws(Exception::class)
    fun setUp() {
        constraintSpec = ImporterFacade.importConstraintSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!,
        )
        hybridRow = HybridRow(constraintSpec!!.rows[1], constraintSpec!!.durations[1])
    }

    @Test
    @Throws(ImportException::class)
    fun testUpdateCounterExampleCells() {
        for (columnId in hybridRow!!.cells.keys) {
            val cell = hybridRow!!.cells[columnId]!!
            Assertions.assertEquals(0, cell.counterExamplesProperty.size)
        }
        Assertions.assertEquals(0, hybridRow!!.duration.counterExamplesProperty.size)
        val typeContext = listOf(TypeInt.INT, TypeBool.BOOL, enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml")!!, typeContext
        )
        hybridRow!!.updateCounterExampleCells(1, concreteSpec)
        for (columnId in hybridRow!!.cells.keys) {
            val cell = hybridRow!!.cells[columnId]!!
            Assertions.assertEquals(50, cell.counterExamplesProperty.size)
        }
        Assertions.assertEquals("50", hybridRow!!.duration.counterExamplesProperty[0])
    }
}