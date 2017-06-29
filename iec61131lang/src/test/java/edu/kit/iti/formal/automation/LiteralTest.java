package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import org.junit.Test;

/**
 * @author Alexander Weigl
 * @version 1 (03.03.17)
 */
public class ValueFactoryTest {
    @Test
    public void makeInt() throws Exception {
      /*  Assert.assertEquals((Integer) 0, ValueFactory.makeInt().getValue());
        Assert.assertEquals((Long) 161141L,
                ValueFactory.makeInt(161141).getValue());
    */
    }

    @Test
    public void makeUInt() throws Exception {

    }

    @Test
    public void makeSInt() throws Exception {

    }

    @Test
    public void makeLInt() throws Exception {

    }

    @Test
    public void makeDInt() throws Exception {

    }

    @Test
    public void makeInt1() throws Exception {

    }

    @Test
    public void makeSInt1() throws Exception {

    }

    @Test
    public void makeLInt1() throws Exception {

    }

    @Test
    public void makeDInt1() throws Exception {

    }

    @Test
    public void makeAnyBit() throws Exception {

    }

    @Test
    public void makeBool() throws Exception {

    }

    @Test
    public void makeWord() throws Exception {

    }

    @Test
    public void makeDWord() throws Exception {

    }

    @Test
    public void makeLWord() throws Exception {

    }

    @Test
    public void parseLiteral() throws Exception {

    }

    @Test
    public void parseBitLiteral() throws Exception {

    }

    @Test
    public void parseBitLiteral1() throws Exception {

    }

    @Test
    public void parseIntegerLiteral() throws Exception {

    }

    @Test
    public void parseIntegerLiteral1() throws Exception {

    }

    @Test
    public void makeEnumeratedValue() throws Exception {

    }

    @Test
    public void makeEnumeratedValue1() throws Exception {

    }

    @Test
    public void parseStringLiteral() throws Exception {

    }

    @Test
    public void parseStringLiteral1() throws Exception {

    }

    @Test
    public void parseTimeLiteral() throws Exception {

    }

    @Test
    public void parseTimeLiteral1() throws Exception {

    }

    @Test
    public void getPrefix() throws Exception {

    }

    @Test
    public void makeBool1() throws Exception {

    }

    @Test
    public void makeBool2() throws Exception {

    }

    @Test
    public void makeBool3() throws Exception {

    }

    @Test
    public void parseRealLiteral() throws Exception {

    }

    @Test
    public void parseRealLiteral1() throws Exception {

    }

    @Test
    public void parseDateAndTimeLiteral() throws Exception {

    }

    @Test
    public void parseDateAndTimeLiteral1() throws Exception {

    }

    @Test
    public void parseDateLiteral() throws Exception {

    }

    @Test
    public void parseDateLiteral1() throws Exception {

    }

    @Test
    public void parseTimeOfDayLiteral() throws Exception {

    }

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorHour()
            throws Exception {
     //   ValueFactory.parseTimeOfDayLiteral("200:61").getValue();
    }

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorMin()
            throws Exception {
       // ValueFactory.parseTimeOfDayLiteral("20:610:20").getValue();
    }

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorSec()
            throws Exception {
        //  ValueFactory.parseTimeOfDayLiteral("20:61:a").getValue();
    }

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorMsec()
            throws Exception {
        //    ValueFactory.parseTimeOfDayLiteral("200:61:1.6a").getValue();
    }

    @Test
    public void parseTimeOfDayLiteral1() throws Exception {
      /*  Assert.assertEquals(new TimeofDayData(20, 61, 00, 00),
                ValueFactory.parseTimeOfDayLiteral("20:61").getValue());

        Assert.assertEquals(new TimeofDayData(20, 61, 10, 00),
                ValueFactory.parseTimeOfDayLiteral("20:61:10").getValue());

        Assert.assertEquals(new TimeofDayData(20, 61, 62, 1005),
                ValueFactory.parseTimeOfDayLiteral("20:61:62.1005").getValue());*/
    }
}
