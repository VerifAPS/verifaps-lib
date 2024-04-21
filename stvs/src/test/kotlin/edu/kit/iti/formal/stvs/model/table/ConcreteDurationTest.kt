package edu.kit.iti.formal.stvs.model.table

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class ConcreteDurationTest {
    private var durationA = ConcreteDuration(1, 2)

    @Test
    fun testGetDuration() {
        Assertions.assertEquals(2, durationA.duration.toLong())
    }

    @Test
    fun testGetBeginCycle() {
        Assertions.assertEquals(1, durationA.beginCycle.toLong())
    }

    @Test
    fun testToString() {
        Assertions.assertEquals("2", durationA.toString())
    }

    @Test
    fun testGetEndCycle() {
        var duration = ConcreteDuration(3, 4)
        Assertions.assertEquals(7, duration.endCycle.toLong())
        duration = ConcreteDuration(0, 0)
        Assertions.assertEquals(0, duration.endCycle.toLong())
        duration = ConcreteDuration(1, 0)
        Assertions.assertEquals(1, duration.endCycle.toLong())
    }

    @Test//(expected = IllegalArgumentException::class)
    fun testConstructorInvalidBeginCycle() {
        assertFailsWith<IllegalArgumentException> {
            ConcreteDuration(-1, 1)
        }
    }

    @Test//(expected = IllegalArgumentException::class)
    fun testConstructorInvalidDuration() {
        assertFailsWith<IllegalArgumentException> {
            ConcreteDuration(1, -1)
        }
    }

    @Test
    fun testEquals() {
        val durationB = ConcreteDuration(1, 2)
        Assertions.assertEquals(durationA, durationB)
        val durationC = ConcreteDuration(1, 3)
        Assertions.assertNotEquals(durationA, durationC)
        val durationD = ConcreteDuration(2, 2)
        Assertions.assertNotEquals(durationA, durationD)
        val durationE = ConstraintDuration("2")
        Assertions.assertNotEquals(durationA, durationE)
        Assertions.assertNotEquals(durationA, null)
    }
}
