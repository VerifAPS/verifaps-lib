package edu.kit.iti.formal.automation.datatypes.values

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
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
import edu.kit.iti.formal.automation.sfclang.getIntegerLiteralValue
import edu.kit.iti.formal.automation.st.ast.Literal
import org.apache.commons.lang3.NotImplementedException
import java.math.BigDecimal
import java.math.BigInteger

class ValueTransformation(val literal: Literal) : DefaultDataTypeVisitor<Value<*, *>>() {
    override fun defaultVisit(obj: Any): Value<*, *>? {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(bool: AnyBit.BOOL): Value<*, *>? {
        if (literal.textValue!!.equals("true", ignoreCase = true))
            return TRUE
        if (literal.textValue!!.equals("false", ignoreCase = true))
            return FALSE

        throw IllegalArgumentException("Boolean literal isType not true or false; got: " + literal.text)
    }

    override fun visit(anyInt: AnyInt): Value<*, *>? {
        val s = getIntegerLiteralValue(literal.text, literal.signed)
        return VAnyInt(DataTypes.findSuitableInteger(s), s)
    }

    override fun visit(anyInt: INT): Value<*, *>? = getInteger(anyInt)

    private fun getInteger(anyInt: AnyInt): Value<*, *> {
        val s = getIntegerLiteralValue(literal.textValue!!, literal.signed)
        return VAnyInt(DataTypes.findSuitableInteger(s), s)
    }

    override fun visit(anyInt: SINT): Value<*, *>? {
        return getInteger(anyInt)

    }

    private fun typeMismatch(v: Value<*, *>, anyInt: AnyDt): IllegalStateException {
        return IllegalStateException("expected: " + anyInt + " got:" + v.dataType)
    }

    override fun visit(anyInt: DINT): Value<*, *>? {
        return getInteger(anyInt)

    }

    override fun visit(anyInt: LINT): Value<*, *>? {
        return getInteger(anyInt)
    }

    override fun visit(anyInt: UDINT): Value<*, *>? {
        return getInteger(anyInt)

    }

    override fun visit(anyInt: USINT) = getInteger(anyInt)

    override fun visit(anyInt: ULINT) = getInteger(anyInt)

    override fun visit(anyInt: UINT) = getInteger(anyInt)

    override fun visit(real: AnyReal.REAL) = VAnyReal(real, BigDecimal(literal.textValue!!))

    override fun visit(real: AnyReal.LREAL) = VAnyReal(real, BigDecimal(literal.textValue!!))

    override fun visit(dateAndTime: AnyDate.DATE_AND_TIME) =
            throw NotImplementedException("DateAndTime isType not implemented")

    override fun visit(timeOfDay: AnyDate.TIME_OF_DAY) =
            throw NotImplementedException("TIME_OF_DAY isType not implemented")

    override fun visit(date: AnyDate.DATE) = throw NotImplementedException("DATE datatype not supported")

    override fun visit(enumerateType: EnumerateType): Value<*, *>? {
        if (!enumerateType.allowedValues.contains(literal.textValue)) {
            throw RuntimeException("Enum constant " + literal.text + " isType not defined in " + enumerateType.name)
        }
        return VAnyEnum(enumerateType, literal.textValue!!)
    }

    override fun visit(timeType: TimeType): Value<*, *>? = VTime(timeType, TimeData(literal.textValue!!))
    override fun visit(rangeType: RangeType): Value<*, *>? = VAnyInt(rangeType, BigInteger(literal.text))
    //  override fun visit(string: IECString.STRING): Value<*, *>? = VIECString(string, literal.text)
    //   override fun visit(wString: IECString.WSTRING): Value<*, *>? = VIECString(wString, literal.text)
}
