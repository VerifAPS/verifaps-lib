package edu.kit.iti.formal.automation.datatypes;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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
 * <p>DataTypeVisitor interface.</p>
 *
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public interface DataTypeVisitor<T> {
    /**
     * <p>visit.</p>
     *
     * @param anyBit a {@link edu.kit.iti.formal.automation.datatypes.AnyBit} object.
     * @return a T object.
     */
    T visit(AnyBit anyBit);

    /**
     * <p>visit.</p>
     *
     * @param dateAndTime a {@link edu.kit.iti.formal.automation.datatypes.AnyDate.DateAndTime} object.
     * @return a T object.
     */
    T visit(AnyDate.DateAndTime dateAndTime);

    /**
     * <p>visit.</p>
     *
     * @param timeOfDay a {@link edu.kit.iti.formal.automation.datatypes.AnyDate.TimeOfDay} object.
     * @return a T object.
     */
    T visit(AnyDate.TimeOfDay timeOfDay);

    /**
     * <p>visit.</p>
     *
     * @param date a {@link edu.kit.iti.formal.automation.datatypes.AnyDate.Date} object.
     * @return a T object.
     */
    T visit(AnyDate.Date date);

    /**
     * <p>visit.</p>
     *
     * @param anyInt a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     * @return a T object.
     */
    T visit(AnyInt anyInt);

    /**
     * <p>visit.</p>
     *
     * @param enumerateType a {@link edu.kit.iti.formal.automation.datatypes.EnumerateType} object.
     * @return a T object.
     */
    T visit(EnumerateType enumerateType);

    /**
     * <p>visit.</p>
     *
     * @param timeType a {@link edu.kit.iti.formal.automation.datatypes.TimeType} object.
     * @return a T object.
     */
    T visit(TimeType timeType);

    /**
     * <p>visit.</p>
     *
     * @param field a {@link edu.kit.iti.formal.automation.datatypes.RecordType.Field} object.
     * @return a T object.
     */
    T visit(RecordType.Field field);

    /**
     * <p>visit.</p>
     *
     * @param rangeType a {@link edu.kit.iti.formal.automation.datatypes.RangeType} object.
     * @return a T object.
     */
    T visit(RangeType rangeType);

    /**
     * <p>visit.</p>
     *
     * @param recordType a {@link edu.kit.iti.formal.automation.datatypes.RecordType} object.
     * @return a T object.
     */
    T visit(RecordType recordType);

    /**
     * <p>visit.</p>
     *
     * @param pointerType a {@link edu.kit.iti.formal.automation.datatypes.PointerType} object.
     * @return a T object.
     */
    T visit(PointerType pointerType);

    /**
     * <p>visit.</p>
     *
     * @param string a {@link edu.kit.iti.formal.automation.datatypes.IECString.String} object.
     * @return a T object.
     */
    T visit(IECString.String string);

    /**
     * <p>visit.</p>
     *
     * @param wString a {@link edu.kit.iti.formal.automation.datatypes.IECString.WString} object.
     * @return a T object.
     */
    T visit(IECString.WString wString);

    /**
     * <p>visit.</p>
     *
     * @param iecArray a {@link edu.kit.iti.formal.automation.datatypes.IECArray} object.
     * @return a T object.
     */
    T visit(IECArray iecArray);

    /**
     * <p>visit.</p>
     *
     * @param anyNum a {@link edu.kit.iti.formal.automation.datatypes.AnyNum} object.
     * @return a T object.
     */
    T visit(AnyNum anyNum);

    T visit(ClassDataType classDataType);
}
