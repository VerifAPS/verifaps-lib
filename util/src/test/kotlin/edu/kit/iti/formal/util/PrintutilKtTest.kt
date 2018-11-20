package edu.kit.iti.formal.util

import org.junit.Assert
import org.junit.Test

class PrintutilKtTest {

    @Test
    fun times1() = Assert.assertEquals("aaa", "a" * 3)

    @Test
    fun times2() = Assert.assertEquals("a", "a" * 1)

    @Test
    fun times3() = Assert.assertEquals("", "a" * 0)

    @Test
    fun times4() = Assert.assertEquals("", "a" * (-1))

    @Test
    fun center1() =
            Assert.assertEquals("  1234567 ",
                    "1234567".center(10))

    @Test
    fun center2() =
            Assert.assertEquals("..1234567.",
                    "1234567".center(10, '.'))

    @Test
    fun center3() =
            Assert.assertEquals("1234567",
                    "1234567".center(1))

    @Test
    fun center4() =
            Assert.assertEquals("1234567",
                    "1234567".center(-1))
}