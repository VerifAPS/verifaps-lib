package edu.kit.iti.formal.automation.smt


import edu.kit.iti.formal.automation.smt.DefaultS2STranslator.Companion
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.math.BigInteger

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
class DefaultS2STranslatorTest {
    @Test
    @Throws(Exception::class)
    fun testPaddedString() {
        assertEquals("             abc",
                String(Companion.paddedString(16, ' ', "abc")))

        assertEquals("00001111",
                String(Companion.paddedString(8, '0', "1111")))

        assertEquals("1111",
                String(Companion.paddedString(0, '0', "1111")))
    }

    @Test
    @Throws(Exception::class)
    fun testTwoComplement() {
        assertEquals("00000001",
                Companion.twoComplement(BigInteger.ONE, 8))
        assertEquals("11111111",
                Companion.twoComplement(BigInteger.ONE.negate(), 8))
    }

}
