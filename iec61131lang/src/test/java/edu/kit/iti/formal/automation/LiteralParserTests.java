package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec61131lang
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.values.TimeofDayData;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.st.ast.Literal;
import org.junit.Assert;
import org.junit.Test;

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
public class LiteralParserTests {

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorHour()
            throws Exception {
        TimeofDayData.parse("200:61");
    }

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorMin()
            throws Exception {
        TimeofDayData.parse("20:610:20");
    }

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorSec()
            throws Exception {
        TimeofDayData.parse("20:61:a");
    }

    @Test(expected = IllegalArgumentException.class)
    public void parseTimeOfDayLiteralErrorMsec()
            throws Exception {
        TimeofDayData.parse("200:61:1.6a");
    }

    @Test
    public void parseTimeOfDayLiteral1() throws Exception {
        Assert.assertEquals(new TimeofDayData(20, 61, 00, 00),
                TimeofDayData.parse("20:61").getValue());

        Assert.assertEquals(new TimeofDayData(20, 61, 10, 00),
                TimeofDayData.parse("20:61:10").getValue());

        Assert.assertEquals(new TimeofDayData(20, 61, 62, 1005),
                TimeofDayData.parse("20:61:62.1005").getValue());
    }

}
