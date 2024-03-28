package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.expressions.ValueInt

import javafx.beans.property.SimpleStringProperty
import org.junit.Assert
import org.junit.Assert.assertEquals
import org.junit.Before
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class ConcreteCellTest {
    private var cellA: ConcreteCell? = null

    @Before
    fun setUp() {
        cellA = ConcreteCell(ValueInt(4))
    }

    @Test
    fun testGetValue() {
        assertEquals(ValueInt(4), cellA!!.value)
    }

    @Test
    fun testToString() {
        assertEquals("ValueInt(4)", cellA.toString())
    }

    @Test
    fun testGetAsString() {
        assertEquals("ValueInt(4)", cellA!!.asString)
    }

    @Test
    fun testStringRepresentationProperty() {
        assertEquals(SimpleStringProperty("ValueInt(4)").get(), cellA!!.stringRepresentationProperty.get())
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val cellB = ConcreteCell(ValueInt(4))
        assertEquals(cellA, cellB)
        val cellC = ConcreteCell(ValueInt(2))
        Assert.assertNotEquals(cellA, cellC)
        val cellD = ConcreteCell(ValueBool.TRUE)
        Assert.assertNotEquals(cellA, cellD)
        val cellE = ConstraintCell("4")
        Assert.assertNotEquals(cellA, cellE)
        Assert.assertNotEquals(cellA, null)
    }
}