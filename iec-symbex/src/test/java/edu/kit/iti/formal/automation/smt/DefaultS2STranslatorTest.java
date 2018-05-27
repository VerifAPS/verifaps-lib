package edu.kit.iti.formal.automation.smt;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

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
