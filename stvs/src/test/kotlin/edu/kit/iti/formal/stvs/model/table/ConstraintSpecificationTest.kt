package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 25.02.17.
 */
class ConstraintSpecificationTest {
    private var constraintSpec: ConstraintSpecification? = null

    @BeforeEach
    @Throws(ImportException::class)
    fun setUp() {
        constraintSpec = ImporterFacade.importConstraintSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!
        )
    }

    @Test
    fun testCopyConstructor() {
        val clone = ConstraintSpecification(constraintSpec!!)
        Assertions.assertNotSame(clone, constraintSpec)
        Assertions.assertEquals(clone, constraintSpec)
    }

    @Test
    @Throws(ImportException::class)
    fun testEquals() {
        var equalSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!
        )
        Assertions.assertEquals(equalSpec, constraintSpec)
        Assertions.assertNotEquals(null, constraintSpec)
        equalSpec.comment = "I am a comment"
        Assertions.assertNotEquals(constraintSpec, equalSpec)
        equalSpec = ImporterFacade.importConstraintSpec(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!
        )
        equalSpec.durations[0] = ConstraintDuration("4")
        Assertions.assertNotEquals(constraintSpec, equalSpec)
    }

    @Test
    fun testOnSpecIOVariableNameChanged() {
        // Change name of SpecIoVariable (column header); change should propagate through the rows
        // and columns
        val oldSpecIoVarName = constraintSpec!!.columnHeaders[0].name
        constraintSpec!!.columnHeaders[0].name = "SomeNewName"
        for (row in constraintSpec!!.rows) {
            Assertions.assertTrue(row.cells.containsKey("SomeNewName"))
            Assertions.assertFalse(row.cells.containsKey(oldSpecIoVarName))
        }
        Assertions.assertNotNull(constraintSpec!!.getColumnByName("SomeNewName"))
        Assertions.assertNotNull(constraintSpec!!.getColumnHeaderByName("SomeNewName"))
    }
}