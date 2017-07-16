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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.st.ast.Literal;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.math.BigInteger;
import java.util.Arrays;

import static edu.kit.iti.formal.automation.datatypes.DataTypes.*;

/**
 * @author Alexander Weigl
 * @version 1 (03.03.17)
 */
@RunWith(Parameterized.class)
public class LiteralTest {
    @Parameterized.Parameter(0)
    public String input;
    @Parameterized.Parameter(1)
    public Any literalDataType;
    @Parameterized.Parameter(2)
    public long value;
    @Parameterized.Parameter(3)
    public Any valueDataType;
    @Parameterized.Parameter(4)
    public boolean explicit;

    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> integers() {
        return Arrays.asList(
                new Object[]{"16#F", ANY_INT, 15, USINT, false},
                new Object[]{("-16#F"), ANY_INT, -15, SINT, false},
                new Object[]{"16#FFFFFDABC", ANY_INT, 68719467196L, LINT, false},
                new Object[]{"8#71164424", ANY_INT, 15001876, DINT, false},
                new Object[]{"SINT#16#F", SINT, 15, SINT, true},
                new Object[]{"-UINT#16#F", UINT, -15, SINT, true},
                new Object[]{"70000", ANY_INT, 70000, DINT, false}
        );
    }


    private Literal getLiteral(String s) {
        return (Literal) IEC61131Facade.getParser(s).constant().accept(new IECParseTreeToAST());
    }

    @Test
    public void testIntegerLiteral() {
        Literal p = getLiteral(input);
        Assert.assertEquals(literalDataType, p.getDataType());
        Assert.assertEquals(explicit, p.isDataTypeExplicit());
        Assert.assertEquals(p.isSigned() ? input.substring(1) : input, p.getText());
        Assert.assertEquals(
                BigInteger.valueOf(value),
                p.asValue().getValue());
        Assert.assertEquals(
                valueDataType, p.asValue().getDataType());
    }

}
