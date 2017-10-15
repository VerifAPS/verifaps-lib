package edu.kit.iti.formal.automation.smt;

import org.junit.Test;

import java.math.BigInteger;

import static edu.kit.iti.formal.automation.smt.DefaultS2STranslator.paddedString;
import static edu.kit.iti.formal.automation.smt.DefaultS2STranslator.twoComplement;
import static org.junit.Assert.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
public class DefaultS2STranslatorTest {
    @Test
    public void testPaddedString() throws Exception {
        assertEquals("             abc",
                new String(paddedString(16, ' ', "abc")));

        assertEquals("00001111",
                new String(paddedString(8, '0', "1111")));

        assertEquals("1111",
                new String(paddedString(0, '0', "1111")));
    }

    @Test
    public void testTwoComplement() throws Exception {
        assertEquals("00000001",
                twoComplement(BigInteger.ONE, 8));
        assertEquals("11111111",
                twoComplement(BigInteger.ONE.negate(), 8));
    }

}