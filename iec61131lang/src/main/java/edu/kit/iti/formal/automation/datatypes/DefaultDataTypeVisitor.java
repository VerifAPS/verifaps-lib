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
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
public abstract class DefaultDataTypeVisitor<T> implements DataTypeVisitor<T> {
    @Override
    public T visit(AnyReal real) {
        return null;
    }

    @Override
    public T visit(AnyReal.Real real) {
        return null;
    }

    @Override
    public T visit(AnyReal.LReal real) {
        return null;
    }

    @Override
    public T visit(AnyBit anyBit) {
        return null;
    }

    @Override
    public T visit(AnyDate.DateAndTime dateAndTime) {
        return null;
    }

    @Override
    public T visit(AnyDate.TimeOfDay timeOfDay) {
        return null;
    }

    @Override
    public T visit(AnyDate.Date date) {
        return null;
    }

    @Override
    public T visit(AnyInt anyInt) {
        return null;
    }

    @Override
    public T visit(EnumerateType enumerateType) {
        return null;
    }

    @Override
    public T visit(TimeType timeType) {
        return null;
    }

    @Override
    public T visit(RangeType rangeType) {
        return null;
    }

    @Override
    public T visit(RecordType recordType) {
        return null;
    }

    @Override
    public T visit(PointerType pointerType) {
        return null;
    }

    @Override
    public T visit(ReferenceType referenceType) {
        return null;
    }

    @Override
    public T visit(IECString.String string) {
        return null;
    }

    @Override
    public T visit(IECString.WString wString) {
        return null;
    }

    @Override
    public T visit(IECArray iecArray) {
        return null;
    }

    @Override
    public T visit(AnyNum anyNum) {
        return null;
    }

    @Override
    public T visit(ClassDataType classDataType) {
        return null;
    }
}
