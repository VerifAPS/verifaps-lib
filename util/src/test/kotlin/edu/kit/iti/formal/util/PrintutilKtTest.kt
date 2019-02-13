package edu.kit.iti.formal.util

import org.junit.jupiter.api.Assertions
 import org.junit.jupiter.api.Test

class PrintutilKtTest {

    @Test
    fun times1() = Assertions.assertEquals("aaa", "a" * 3)

    @Test
    fun times2() = Assertions.assertEquals("a", "a" * 1)

    @Test
    fun times3() = Assertions.assertEquals("", "a" * 0)

    @Test
    fun times4() = Assertions.assertEquals("", "a" * (-1))

    @Test
    fun center1() =
            Assertions.assertEquals("  1234567 ",
                    "1234567".center(10))

    @Test
    fun center2() =
            Assertions.assertEquals("..1234567.",
                    "1234567".center(10, '.'))

    @Test
    fun center3() =
            Assertions.assertEquals("1234567",
                    "1234567".center(1))

    @Test
    fun center4() =
            Assertions.assertEquals("1234567",
                    "1234567".center(-1))
}