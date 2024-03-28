package edu.kit.iti.formal.stvs.model.common

import javafx.beans.InvalidationListener
import javafx.beans.Observable
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import org.junit.Assert
import org.junit.jupiter.api.Test

/**
 * Created by leonk on 18.01.2017.
 */
class SelectionTest {
    @Test
    fun testClearColumnListenerSelection() {
        val wasCalled: BooleanProperty = SimpleBooleanProperty(false)
        val selection = Selection("fgrfg", 4)
        val listener = InvalidationListener { i: Observable? -> wasCalled.set(true) }
        selection.columnProperty().addListener(listener)
        selection.columnProperty().set(null)
        Assert.assertTrue(wasCalled.get())
        Assert.assertTrue(selection.columnProperty().isNull().get())

        wasCalled.set(false)
        selection.columnProperty().removeListener(listener)
        selection.setColumn("Test")
        Assert.assertFalse(wasCalled.get())
        Assert.assertEquals("Test", selection.getColumn().get())
    }

    @Test
    fun testSetRow() {
        val selection = Selection()
        Assert.assertTrue(selection.rowProperty().isNull().get())
        selection.setRow(5)
        Assert.assertEquals(5, selection.getRow().get().toLong())
        Assert.assertEquals(5, selection.rowProperty().get()!!.toLong())
    }
}