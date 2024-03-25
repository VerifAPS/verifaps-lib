package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.*

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class ColumnConfigTest {
    private var config: ColumnConfig? = null

    @BeforeEach
    fun setUp() {
        config = ColumnConfig(130.0)
    }

    @Test
    fun testGetSetColwidth() {
        // default colwidth
        Assertions.assertEquals(100.0, ColumnConfig().width, TestUtils.EPSILON)
        Assertions.assertEquals(130.0, config!!.width, TestUtils.EPSILON)
        config!!.width = 120.0
        Assertions.assertEquals(120.0, config!!.width, TestUtils.EPSILON)
    }

    @Test//(expected = IllegalArgumentException::class)
    fun testIllegalColwidthConstructor() {
        config = ColumnConfig(0.0)
    }

    @Test//(expected = IllegalArgumentException::class)
    fun testSetIllegalWidth() {
        config!!.width = (-1).toDouble()
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical = ColumnConfig(130.0)
        Assertions.assertEquals(identical, config)
        Assertions.assertNotEquals(null, config)
        Assertions.assertEquals(config, config)
        identical.width = 100.0
        Assertions.assertNotEquals(identical, config)
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        val identical = ColumnConfig(130.0)
        Assertions.assertEquals(identical.hashCode().toLong(), config.hashCode().toLong())
        Assertions.assertEquals(config.hashCode().toLong(), config.hashCode().toLong())
        identical.width = 100.0
        Assertions.assertNotEquals(identical.hashCode().toLong(), config.hashCode().toLong())
    }
}