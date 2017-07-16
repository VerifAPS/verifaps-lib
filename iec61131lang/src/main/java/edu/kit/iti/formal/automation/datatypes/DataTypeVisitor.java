package edu.kit.iti.formal.automation.datatypes;

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


/**
 * @param <T>
 * @author Alexander Weigl
 */

public interface DataTypeVisitor<T> {
    T visit(AnyReal real);

    T visit(AnyReal.Real real);

    T visit(AnyReal.LReal real);

    T visit(AnyBit anyBit);

    T visit(AnyDate.DateAndTime dateAndTime);


    T visit(AnyDate.TimeOfDay timeOfDay);


    T visit(AnyDate.Date date);


    default T visit(AnyInt anyInt) {
        return visit((AnyNum) anyInt);
    }

    default T visit(AnySignedInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(AnyUnsignedInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(Int anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(SInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(DInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(LInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(UDInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(USInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(ULInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(UInt anyInt) {
        return visit((AnyInt) anyInt);
    }

    default T visit(AnyBit.Bool bool) {
        return visit((AnyBit) bool);
    }

    default T visit(AnyBit.Byte word) {
        return visit((AnyBit) word);
    }

    default T visit(AnyBit.Word word) {
        return visit((AnyBit) word);
    }

    default T visit(AnyBit.DWord word) {
        return visit((AnyBit) word);
    }

    default T visit(AnyBit.LWord word) {
        return visit((AnyBit) word);
    }


    T visit(EnumerateType enumerateType);

    T visit(TimeType timeType);

    T visit(RangeType rangeType);

    T visit(RecordType recordType);


    T visit(PointerType pointerType);


    T visit(IECString.String string);


    T visit(IECString.WString wString);


    T visit(IECArray iecArray);

    T visit(AnyNum anyNum);

    T visit(ClassDataType classDataType);
}
