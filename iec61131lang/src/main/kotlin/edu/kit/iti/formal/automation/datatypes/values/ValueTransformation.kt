package edu.kit.iti.formal.automation.datatypes.values

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.sfclang.Utils
import edu.kit.iti.formal.automation.st.ast.Literal
import org.apache.commons.lang3.NotImplementedException

import java.math.BigDecimal
import java.math.BigInteger
import java.util.Collections

class ValueTransformation(private val literal: Literal) : DefaultDataTypeVisitor<Value<*, *>>() {

    override fun visit(bool: AnyBit.Bool): Value<*, *>? {
        if (literal.textValue!!.equals("true", ignoreCase = true))
            return Values.VBool.TRUE
        if (literal.textValue!!.equals("false", ignoreCase = true))
            return Values.VBool.FALSE

        throw IllegalArgumentException("Boolean literal is not true or false; got: " + literal.text)
    }

    override fun visit(anyInt: AnyInt): Value<*, *>? {
        val s = Utils.getIntegerLiteralValue(literal.text, literal.isSigned)
        return Values.VAnyInt(DataTypes.findSuitableInteger(s), s)
    }

    override fun visit(anyInt: AnySignedInt): Value<*, *>? {
        val s = Utils.getIntegerLiteralValue(literal.text, literal.isSigned)
        return Values.VAnyInt(DataTypes.findSuitableInteger(s, true), s)
    }

    override fun visit(anyInt: AnyUnsignedInt): Value<*, *>? {
        val s = Utils.getIntegerLiteralValue(literal.text, literal.isSigned)
        return Values.VAnyInt(DataTypes.findSuitableInteger(s, false), s)
    }

    override fun visit(anyInt: Int): Value<*, *>? {
        return getInteger(anyInt)
    }

    private fun getInteger(anyInt: AnyInt): Value<*, *> {
        val s = Utils.getIntegerLiteralValue(literal.textValue, literal.isSigned)
        return Values.VAnyInt(DataTypes.findSuitableInteger(s, setOf<AnyInt>(anyInt)), s)
    }

    override fun visit(anyInt: SInt): Value<*, *>? {
        return getInteger(anyInt)

    }

    private fun typeMismatch(v: Value<*, *>, anyInt: AnyDt): IllegalStateException {
        return IllegalStateException("expected: " + anyInt + " got:" + v.dataType)
    }

    override fun visit(anyInt: DInt): Value<*, *>? {
        return getInteger(anyInt)

    }

    override fun visit(anyInt: LInt): Value<*, *>? {
        return getInteger(anyInt)
    }

    override fun visit(anyInt: UDInt): Value<*, *>? {
        return getInteger(anyInt)

    }

    override fun visit(anyInt: USInt): Value<*, *>? {
        return getInteger(anyInt)

    }

    override fun visit(anyInt: ULInt): Value<*, *>? {
        return getInteger(anyInt)

    }

    override fun visit(anyInt: UInt): Value<*, *>? {
        return getInteger(anyInt)
    }

    override fun visit(real: AnyReal.Real): Value<*, *>? {
        return Values.VAnyReal(real, BigDecimal(literal.textValue!!))
    }

    override fun visit(real: AnyReal.LReal): Value<*, *>? {
        return Values.VAnyReal(real, BigDecimal(literal.textValue!!))
    }

    override fun visit(dateAndTime: AnyDate.DateAndTime): Value<*, *>? {
        throw NotImplementedException("DateAndTime is not implemented")
    }

    override fun visit(timeOfDay: AnyDate.TimeOfDay): Value<*, *>? {
        throw NotImplementedException("TimeOfDay is not implemented")
    }

    override fun visit(date: AnyDate.Date): Value<*, *>? {
        throw NotImplementedException("Date datatype not supported")
    }

    override fun visit(enumerateType: EnumerateType): Value<*, *>? {
        if (!enumerateType.allowedValues.contains(literal.textValue)) {
            throw RuntimeException("Enum constant " + literal.text + " is not defined in " + enumerateType.name)
        }
        return Values.VAnyEnum(enumerateType, literal.textValue)
    }

    override fun visit(timeType: TimeType): Value<*, *>? {
        return Values.VTime(timeType, TimeValue(literal.textValue))
    }

    override fun visit(rangeType: RangeType): Value<*, *>? {
        return Values.VAnyInt(rangeType, BigInteger(literal.text))
    }

    override fun visit(string: IECString.String): Value<*, *>? {
        return Values.VIECString(string, literal.text)
    }

    override fun visit(wString: IECString.WString): Value<*, *>? {
        return Values.VIECString(wString, literal.text)
    }

    companion object {
        /**
         * Cycle time, in milliseconds.
         */
        private val CYCLE_TIME = 10
    }
}
