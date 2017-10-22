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
 * @param <T> return type
 * @author Alexander Weigl
 */

public interface DataTypeVisitor<T> {
    default T defaultVisit(Any any) {
        return null;
    }

    default T visit(AnyReal real) {
        return defaultVisit(real);
    }

    default T visit(AnyReal.Real real) {
        return defaultVisit(real);
    }

    default T visit(AnyReal.LReal real) {
        return defaultVisit(real);
    }

    default T visit(AnyBit anyBit) {
        return defaultVisit(anyBit);
    }

    default T visit(AnyDate.DateAndTime dateAndTime) {
        return defaultVisit(dateAndTime);
    }

    default T visit(AnyDate.TimeOfDay timeOfDay) {
        return defaultVisit(timeOfDay);
    }

    default T visit(AnyDate.Date date) {
        return defaultVisit(date);
    }

    default T visit(AnyReference reference) {
        return defaultVisit(reference);
    }

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

    default T visit(EnumerateType enumerateType) {
        return defaultVisit(enumerateType);
    }

    default T visit(TimeType timeType) {
        return defaultVisit(timeType);
    }

    default T visit(RangeType rangeType) {
        return defaultVisit(rangeType);
    }

    default T visit(RecordType recordType) {
        return defaultVisit(recordType);
    }

    default T visit(PointerType pointerType) {
        return defaultVisit(pointerType);
    }

    default T visit(ReferenceType referenceType) {
        return defaultVisit(referenceType);
    }

    default T visit(IECString.String string) {
        return defaultVisit(string);
    }

    default T visit(IECString.WString wString) {
        return defaultVisit(wString);
    }

    default T visit(IECArray iecArray) {
        return defaultVisit(iecArray);
    }

    default T visit(AnyNum anyNum) {
        return defaultVisit(anyNum);
    }

    default T visit(ClassDataType classDataType) {
        return defaultVisit(classDataType);
    }
}
