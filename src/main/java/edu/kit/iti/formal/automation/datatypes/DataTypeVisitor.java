package edu.kit.iti.formal.automation.datatypes;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public interface DataTypeVisitor<T> {
    T visit(AnyBit anyBit);

    T visit(AnyDate.DateAndTime dateAndTime);

    T visit(AnyDate.TimeOfDay timeOfDay);

    T visit(AnyDate.Date date);

    T visit(AnyInt anyInt);

    T visit(EnumerateType enumerateType);

    T visit(TimeType timeType);

    T visit(RecordType.Field field);

    T visit(RangeType rangeType);

    T visit(RecordType recordType);

    T visit(PointerType pointerType);

    T visit(IECString.String string);

    T visit(IECString.WString wString);

    T visit(IECArray iecArray);

    T visit(AnyNum anyNum);
}
