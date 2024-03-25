package edu.kit.iti.formal.stvs.model.table

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * Created by bal on 25.02.17.
 */
class ConstraintCellTest {
    private var constraintCell = ConstraintCell("Test")
        .also {
            it.comment = "I am a comment!"
        }

    @Test
    fun testCopyConstructor() {
        val clone = ConstraintCell(constraintCell)
        Assertions.assertNotSame(constraintCell, clone)
        Assertions.assertEquals(constraintCell, clone)
    }

    @Test
    fun testEquals() {
        val identical = ConstraintCell("Test")
        identical.comment = "I am a comment!"
        Assertions.assertEquals(constraintCell, identical)
        Assertions.assertNotEquals(constraintCell, null)
        Assertions.assertNotEquals(constraintCell, ConstraintCell("Test"))
    }

    @Test
    fun testToString() {
        Assertions.assertEquals("Test (comment: \"I am a comment!\")", constraintCell.toString())
    }

    @Test
    fun testSetFromString() {
        constraintCell!!.setFromString("Some string")
        Assertions.assertEquals("Some string", constraintCell!!.asString)
    }
}