package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.TestUtils
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by bal on 26.02.17.
 */
class ColumnConfigTest {
    private var config = ColumnConfig(130.0)

    @Test
    fun testGetSetColwidth() {
        // default colwidth
        assertEquals(100.0, ColumnConfig().width, TestUtils.EPSILON)
        assertEquals(130.0, config.width, TestUtils.EPSILON)
        config.width = 120.0
        assertEquals(120.0, config.width, TestUtils.EPSILON)
    }

    @Test
    fun testIllegalColwidthConstructor() {
        assertFailsWith<IllegalArgumentException> {
            config = ColumnConfig(0.0)
        }
    }

    @Test
    fun testSetIllegalWidth() {
        assertFailsWith<IllegalArgumentException> {
            config.width = (-1).toDouble()
        }
    }

    @Test
    fun testEquals() {
        val identical = ColumnConfig(130.0)
        assertEquals(identical, config)
        Assertions.assertNotEquals(null, config)
        assertEquals(config, config)
        identical.width = 100.0
        Assertions.assertNotEquals(identical, config)
    }

    @Test
    fun testHashCode() {
        val identical = ColumnConfig(130.0)
        assertEquals(identical.hashCode().toLong(), config.hashCode().toLong())
        assertEquals(config.hashCode().toLong(), config.hashCode().toLong())
        identical.width = 100.0
        Assertions.assertNotEquals(identical.hashCode().toLong(), config.hashCode().toLong())
    }
}