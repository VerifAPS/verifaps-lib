package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecExporterTest
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.expressions.ValueInt
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 * @author Philipp
 */
class ConcreteSpecificationTest {
    private lateinit var concreteSpec: ConcreteSpecification

    @BeforeEach
    @Throws(Exception::class)
    fun setUp() {
        concreteSpec = ImporterFacade.importConcreteSpec(
            XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_concrete_valid_1.xml")!!,
            listOf(TypeInt, TypeBool)
        )
    }

    @Test
    fun testEmptyConstructor() {
        val emptySpec = ConcreteSpecification(false)
        Assertions.assertEquals(mutableListOf<Any>(), emptySpec.durations)
        Assertions.assertEquals(0, emptySpec.columnHeaders.size)
        Assertions.assertEquals(0, emptySpec.rows.size)
        Assertions.assertEquals(SpecificationTable.DEFAULT_NAME, emptySpec.name)
    }

    @Test
    fun testConcreteValuesForConstraintCell() {
        val expectedCellsA = listOf<ConcreteCell>(
            ConcreteCell(ValueInt(1)),
            ConcreteCell(ValueInt(2)),
            ConcreteCell(ValueInt(3)),
            ConcreteCell(ValueInt(4))
        )
        Assertions.assertEquals(expectedCellsA, concreteSpec.getConcreteValuesForConstraintCell("A", 1))
        val expectedCellsB = listOf<ConcreteCell>(
            ConcreteCell(ValueBool.FALSE),
            ConcreteCell(ValueBool.FALSE)
        )
        Assertions.assertEquals(expectedCellsB, concreteSpec.getConcreteValuesForConstraintCell("B", 0))
        Assertions.assertEquals(mutableListOf<Any>(), concreteSpec.getConcreteValuesForConstraintCell("A", 3))
    }

    @Test
    fun testGetConcreteDurationForConstraintRow() {
        Assertions.assertEquals(null, concreteSpec.getConcreteDurationForConstraintRow(3))
        Assertions.assertEquals(
            ConcreteDuration(2, 4),
            concreteSpec.getConcreteDurationForConstraintRow(1)
        )
    }

    @Test
    fun testCycleToRowNumber() {
        Assertions.assertEquals(2, concreteSpec.cycleToRowNumber(6))
        Assertions.assertEquals(0, concreteSpec.cycleToRowNumber(0))
        Assertions.assertEquals(0, concreteSpec.cycleToRowNumber(1))
        Assertions.assertEquals(1, concreteSpec.cycleToRowNumber(2))
    }

    @Test
    fun testCycleToRowNumberInvalidCycle() {
        assertFailsWith<NoSuchElementException> {
            concreteSpec.cycleToRowNumber(7)
        }
    }

    @Test
    fun testIsCounterexample() {
        Assertions.assertFalse(concreteSpec.isCounterExample)
    }

    @Test
    fun testEquals() {
        val identicalSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_concrete_valid_1.xml")!!,
            listOf(TypeInt, TypeBool)
        )
        Assertions.assertEquals(identicalSpec, concreteSpec)
        val differentSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_concrete_empty.xml")!!,
            listOf(TypeInt, TypeBool)
        )
        Assertions.assertNotEquals(differentSpec, concreteSpec)
        Assertions.assertNotEquals(null, concreteSpec)
    }
}
