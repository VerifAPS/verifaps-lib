package edu.kit.iti.formal.stvs.model.table

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 25.02.17.
 */
class ConstraintDurationTest {
    private var duration: ConstraintDuration? = null

    @BeforeEach
    fun setUp() {
        duration = ConstraintDuration("[2,3]")
        duration!!.comment = "I am a comment!"
    }

    @Test
    fun testCopyConstructor() {
        val clone = ConstraintDuration(duration!!)
        Assertions.assertNotSame(clone, duration)
        Assertions.assertEquals(clone, duration)
    }

    @Test
    fun setFromString() {
        duration!!.setFromString("[4,-]")
        Assertions.assertEquals("[4,-]", duration!!.asString)
    }

    @Test
    fun equals() {
        val identical = ConstraintDuration("[2,3]")
        identical.comment = "I am a comment!"
        Assertions.assertEquals(identical, duration)
        Assertions.assertNotEquals(duration, null)
        identical.setFromString("[4,-]")
        Assertions.assertNotEquals(identical, duration)
    }
}