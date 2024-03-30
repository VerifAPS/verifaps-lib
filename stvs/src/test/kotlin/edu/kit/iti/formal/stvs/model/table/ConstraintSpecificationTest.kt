package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import org.junit.jupiter.api.*

/**
 * Created by bal on 25.02.17.
 */
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
class ConstraintSpecificationTest {
    private var constraintSpec =
        ImporterFacade.importConstraintSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml")
        )

    @Test
    @Order(1)
    fun testCopyConstructor() {
        val clone = ConstraintSpecification(constraintSpec)
        Assertions.assertNotSame(clone, constraintSpec)
        Assertions.assertEquals(clone, constraintSpec)
    }

    @Test
    @Order(2)
    fun testEquals() {
        var equalSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml")
        )
        Assertions.assertEquals(equalSpec, constraintSpec)
        Assertions.assertNotEquals(null, constraintSpec)
        equalSpec.comment = "I am a comment"
        Assertions.assertNotEquals(constraintSpec, equalSpec)
        equalSpec = ImporterFacade.importConstraintSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml")
        )
        equalSpec.durations[0] = ConstraintDuration("4")
        Assertions.assertNotEquals(constraintSpec, equalSpec)
    }

    @Test
    @Order(3)
    fun testOnSpecIOVariableNameChanged() {
        // Change name of SpecIoVariable (column header); change should propagate through the rows
        // and columns
        val oldSpecIoVarName = constraintSpec.columnHeaders[0].name
        constraintSpec.columnHeaders[0].name = "SomeNewName"
        for (row in constraintSpec.rows) {
            Assertions.assertTrue(row.cells.containsKey("SomeNewName"))
            Assertions.assertFalse(row.cells.containsKey(oldSpecIoVarName))
        }
        Assertions.assertNotNull(constraintSpec.getColumnByName("SomeNewName"))
        Assertions.assertNotNull(constraintSpec.getColumnHeaderByName("SomeNewName"))
    }
}