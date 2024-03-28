package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.logic.specification.smtlib.BitvectorUtils.hexFromInt
import edu.kit.iti.formal.stvs.logic.specification.smtlib.BitvectorUtils.intFromHex
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * Created by leonk on 21.02.2017.
 */
class BitvectorUtilsTest {
    @Test
    fun testEquality() {
        for (i in -32768..32767) {
            Assertions.assertEquals(i.toLong(), intFromHex(hexFromInt(i, 4), true).toLong())
        }
        for (i in 0..65535) {
            Assertions.assertEquals(i.toLong(), intFromHex(hexFromInt(i, 4), false).toLong())
        }
    }

    @Test
    fun testCritical() {
        Assertions.assertEquals(32767, intFromHex("#x7FFF", true).toLong())
        Assertions.assertEquals(-32768, intFromHex("#x8000", true).toLong())
        Assertions.assertEquals(0, intFromHex("#x0000", true).toLong())
        Assertions.assertEquals(-1, intFromHex("#xFFFF", true).toLong())

        Assertions.assertEquals(32767, intFromHex("#x7FFF", false).toLong())
        Assertions.assertEquals(32768, intFromHex("#x8000", false).toLong())
        Assertions.assertEquals(0, intFromHex("#x0000", false).toLong())
        Assertions.assertEquals(65535, intFromHex("#xFFFF", false).toLong())
    }

    @Test
    fun testWrongFormat() {
        assertFailsWith<IllegalArgumentException> { intFromHex("notvalid", true) }
    }

    @Test
    fun testNull() {
        assertFailsWith<IllegalArgumentException> {
            intFromHex(null, false)
        }
    }
}