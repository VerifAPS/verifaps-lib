package edu.kit.iti.formal.automation

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.Literal
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (03.03.17)
 */
@RunWith(Parameterized::class)
class IntegerLiteralTest {
    @Parameterized.Parameter(0)
    var input: String? = null
    @Parameterized.Parameter(1)
    var literalDataType: AnyDt? = null
    @Parameterized.Parameter(2)
    var value: Long = 0
    @Parameterized.Parameter(3)
    var valueDataType: AnyDt? = null
    @Parameterized.Parameter(4)
    var explicit: Boolean = false


    private fun getLiteral(s: String?): Literal {
        return IEC61131Facade.getParser(s!!).constant().accept(IECParseTreeToAST()) as Literal
    }

    @Test
    fun testIntegerLiteral() {
        val p = getLiteral(input)
        Assert.assertEquals(literalDataType, p.dataType)
        Assert.assertEquals(explicit, p.dataTypeExplicit)
        Assert.assertEquals(input, p.text)
        //Assert.assertEquals(
        //        BigInteger.valueOf(value),
        //        p.asValue().getValue());
        //Assert.assertEquals(
        //        valueDataType, p.asValue().getDataType());
    }

    companion object {
        @Parameterized.Parameters(name = "{0}")
        fun integers(): Iterable<Array<Any>> {
            return Arrays.asList(
                    arrayOf("16#F", ANY_INT, 15, USINT, false),
                    arrayOf("-16#F", ANY_INT, -15, SINT, false),
                    arrayOf("16#FFFFFDABC", ANY_INT, 68719467196L, LINT, false),
                    arrayOf("8#71164424", ANY_INT, 15001876, DINT, false),
                    arrayOf("SINT#16#F", SINT, 15, SINT, true),
                    arrayOf("-UINT#16#F", UINT, -15, SINT, true),
                    arrayOf("70000", ANY_INT, 70000, DINT, false),
                    arrayOf("-1", ANY_INT, -1, INT, false)
            )
        }
    }

}
