package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecExporterTest
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.expressions.ValueInt
import junit.framework.TestCase
import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Benjamin Alt
 * @author Philipp
 */
class ConcreteSpecificationTest {
    private var concreteSpec: ConcreteSpecification? = null

    @Before
    @Throws(Exception::class)
    fun setUp() {
        concreteSpec = ImporterFacade.importConcreteSpec(
            XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_concrete_valid_1.xml"),
            listOf(TypeInt.INT, TypeBool.BOOL)
        )
    }

    @Test
    fun testEmptyConstructor() {
        val emptySpec = ConcreteSpecification(false)
        TestCase.assertEquals(mutableListOf<Any>(), emptySpec.durations)
        TestCase.assertEquals(0, emptySpec.columnHeaders.size)
        TestCase.assertEquals(0, emptySpec.rows.size)
        TestCase.assertEquals(SpecificationTable.DEFAULT_NAME, emptySpec.name)
    }

    @Test
    fun testConcreteValuesForConstraintCell() {
        val expectedCellsA = listOf<ConcreteCell>(
            ConcreteCell(ValueInt(1)),
            ConcreteCell(ValueInt(2)),
            ConcreteCell(ValueInt(3)),
            ConcreteCell(ValueInt(4))
        )
        TestCase.assertEquals(
            expectedCellsA,
            concreteSpec!!.getConcreteValuesForConstraintCell("A", 1)
        )
        val expectedCellsB = listOf<ConcreteCell>(
            ConcreteCell(ValueBool.FALSE),
            ConcreteCell(ValueBool.FALSE)
        )
        TestCase.assertEquals(expectedCellsB, concreteSpec!!.getConcreteValuesForConstraintCell("B", 0))
        TestCase.assertEquals(mutableListOf<Any>(), concreteSpec!!.getConcreteValuesForConstraintCell("A", 3))
    }

    @Test
    fun testGetConcreteDurationForConstraintRow() {
        TestCase.assertEquals(Optional.empty<Any>(), concreteSpec!!.getConcreteDurationForConstraintRow(3))
        TestCase.assertEquals(
            Optional.of(ConcreteDuration(2, 4)),
            concreteSpec.getConcreteDurationForConstraintRow(1)
        )
    }

    @Test
    fun testCycleToRowNumber() {
        TestCase.assertEquals(2, concreteSpec!!.cycleToRowNumber(6))
        TestCase.assertEquals(0, concreteSpec!!.cycleToRowNumber(0))
        TestCase.assertEquals(0, concreteSpec!!.cycleToRowNumber(1))
        TestCase.assertEquals(1, concreteSpec!!.cycleToRowNumber(2))
    }

    @Test(expected = IllegalArgumentException::class)
    fun testCycleToRowNumberInvalidCycle() {
        concreteSpec!!.cycleToRowNumber(7)
    }

    @Test
    fun testIsCounterexample() {
        Assert.assertFalse(concreteSpec!!.isCounterExample)
    }

    @Test
    fun testEquals() {
        val identicalSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_concrete_valid_1.xml"),
            listOf(TypeInt.INT, TypeBool.BOOL)
        )
        TestCase.assertEquals(identicalSpec, concreteSpec)
        val differentSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_concrete_empty.xml"),
            listOf(TypeInt.INT, TypeBool.BOOL)
        )
        Assert.assertNotEquals(differentSpec, concreteSpec)
        Assert.assertNotEquals(null, concreteSpec)
    }
}
