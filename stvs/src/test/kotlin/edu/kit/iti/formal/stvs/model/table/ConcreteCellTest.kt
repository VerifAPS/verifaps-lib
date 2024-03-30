package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.expressions.ValueInt
import javafx.beans.property.SimpleStringProperty
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class ConcreteCellTest {
    private var cellA = ConcreteCell(ValueInt(4))

    @Test
    fun testGetValue() {
        Assertions.assertEquals(ValueInt(4), cellA.value)
    }

    @Test
    fun testToString() {
        Assertions.assertEquals("ValueInt(4)", cellA.toString())
    }

    @Test
    fun testGetAsString() {
        Assertions.assertEquals("ValueInt(4)", cellA.asString)
    }

    @Test
    fun testStringRepresentationProperty() {
        Assertions.assertEquals(SimpleStringProperty("ValueInt(4)").get(), cellA.stringRepresentationProperty.get())
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val cellB = ConcreteCell(ValueInt(4))
        Assertions.assertEquals(cellA, cellB)
        val cellC = ConcreteCell(ValueInt(2))
        Assertions.assertNotEquals(cellA, cellC)
        val cellD = ConcreteCell(ValueBool.TRUE)
        Assertions.assertNotEquals(cellA, cellD)
        val cellE = ConstraintCell("4")
        Assertions.assertNotEquals(cellA, cellE)
        Assertions.assertNotEquals(cellA, null)
    }
}