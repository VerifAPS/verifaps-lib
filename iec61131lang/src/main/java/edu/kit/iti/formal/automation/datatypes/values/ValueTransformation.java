package edu.kit.iti.formal.automation.datatypes.values;

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

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.sfclang.Utils;
import edu.kit.iti.formal.automation.st.ast.Literal;
import org.apache.commons.lang3.NotImplementedException;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collections;

public class ValueTransformation extends DefaultDataTypeVisitor<Value> {
    private final Literal literal;

    public ValueTransformation(Literal literal) {
        this.literal = literal;
    }

    @Override
    public Value visit(AnyBit.Bool bool) {
        if (literal.getTextValue().equalsIgnoreCase("true"))
            return Values.VBool.TRUE;
        if (literal.getTextValue().equalsIgnoreCase("false"))
            return Values.VBool.FALSE;

        throw new IllegalArgumentException("Boolean literal is not true or false; got: " + literal.getText());
    }

    @Override
    public Value visit(AnyInt anyInt) {
        BigInteger s = Utils.getIntegerLiteralValue(literal.getText(), literal.isSigned());
        return new Values.VAnyInt(DataTypes.findSuitableInteger(s), s);
    }

    @Override
    public Value visit(AnySignedInt anyInt) {
        BigInteger s = Utils.getIntegerLiteralValue(literal.getText(), literal.isSigned());
        return new Values.VAnyInt(DataTypes.findSuitableInteger(s, true), s);
    }

    @Override
    public Value visit(AnyUnsignedInt anyInt) {
        BigInteger s = Utils.getIntegerLiteralValue(literal.getText(), literal.isSigned());
        return new Values.VAnyInt(DataTypes.findSuitableInteger(s, false), s);
    }

    @Override
    public Value visit(Int anyInt) {
        return getInteger(anyInt);
    }

    private Value getInteger(AnyInt anyInt) {
        BigInteger s = Utils.getIntegerLiteralValue(literal.getTextValue(), literal.isSigned());
        return new Values.VAnyInt(DataTypes.findSuitableInteger(s, Collections.singleton(anyInt)), s);
    }

    @Override
    public Value visit(SInt anyInt) {
        return getInteger(anyInt);

    }

    private IllegalStateException typeMismatch(Value v, Any anyInt) {
        return new IllegalStateException("expected: " + anyInt + " got:" + v.getDataType());
    }

    @Override
    public Value visit(DInt anyInt) {
        return getInteger(anyInt);

    }

    @Override
    public Value visit(LInt anyInt) {
        return getInteger(anyInt);
    }

    @Override
    public Value visit(UDInt anyInt) {
        return getInteger(anyInt);

    }

    @Override
    public Value visit(USInt anyInt) {
        return getInteger(anyInt);

    }

    @Override
    public Value visit(ULInt anyInt) {
        return getInteger(anyInt);

    }

    @Override
    public Value visit(UInt anyInt) {
        return getInteger(anyInt);
    }

    @Override
    public Value visit(AnyReal.Real real) {
        return new Values.VAnyReal(real, new BigDecimal(literal.getTextValue()));
    }

    @Override
    public Value visit(AnyReal.LReal real) {
        return new Values.VAnyReal(real, new BigDecimal(literal.getTextValue()));
    }

    @Override
    public Value visit(AnyDate.DateAndTime dateAndTime) {
        throw new NotImplementedException("DateAndTime is not implemented");
    }

    @Override
    public Value visit(AnyDate.TimeOfDay timeOfDay) {
        throw new NotImplementedException("TimeOfDay is not implemented");
    }

    @Override
    public Value visit(AnyDate.Date date) {
        throw new NotImplementedException("Date datatype not supported");
    }

    @Override
    public Value visit(EnumerateType enumerateType) {
        if (!enumerateType.getAllowedValues().contains(literal.getTextValue())) {
            throw new RuntimeException("Enum constant " + literal.getText() + " is not defined in " + enumerateType.getName());
        }
        return new Values.VAnyEnum(enumerateType, literal.getTextValue());
    }

    @Override
    public Value visit(TimeType timeType) {
        throw new NotImplementedException("time data type not supported");
    }

    @Override
    public Value visit(RangeType rangeType) {
        return new Values.VAnyInt(rangeType.getBase(),
                new BigInteger(literal.getText()));
    }

    @Override
    public Value visit(IECString.String string) {
        return new Values.VIECString(string, literal.getText());
    }

    @Override
    public Value visit(IECString.WString wString) {
        return new Values.VIECString(wString, literal.getText());
    }
}
