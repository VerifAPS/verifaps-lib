package edu.kit.iti.formal.automation.smv;

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.IllegalTypeException;
import edu.kit.iti.formal.smv.ast.GroundDataType;
import edu.kit.iti.formal.smv.ast.SMVType;

import java.util.Arrays;
import java.util.HashMap;
import java.util.function.Function;

/**
 * Created by weigl on 11.12.16.
 */
public class DataTypeTranslator implements DataTypeVisitor<SMVType> {
    public static final DataTypeTranslator INSTANCE = new DataTypeTranslator();

    /*private HashMap<Any, SMVType> map = new HashMap<>();

    public DataTypeTranslator() {
        map.put(AnyInt.INT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 16));
        map.put(AnyInt.LINT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 64));
        map.put(AnyInt.SINT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 8));
        map.put(AnyInt.DINT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 32));

        map.put(AnyInt.UINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 16));
        map.put(AnyInt.ULINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 64));
        map.put(AnyInt.USINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 8));
        map.put(AnyInt.UDINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 32));


        map.put(AnyBit.WORD, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 16));
        map.put(AnyBit.DWORD, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 32));
        map.put(AnyBit.LWORD, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 64));
        map.put(AnyBit.BYTE, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 8));

        map.put(AnyBit.BOOL, SMVType.BOOLEAN);
    }*/

    @Override
    public SMVType visit(AnyBit anyBit) {
        if (anyBit == AnyBit.BOOL) {
            return SMVType.BOOLEAN;
        }
        return new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD,
                anyBit.getBitLength());
    }

    @Override
    public SMVType visit(AnyDate.DateAndTime dateAndTime) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(AnyDate.TimeOfDay timeOfDay) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(AnyDate.Date date) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(AnyInt inttype) {
        return new SMVType.SMVTypeWithWidth(
                inttype.isSigned() ?
                        GroundDataType.SIGNED_WORD :
                        GroundDataType.UNSIGNED_WORD, inttype.getBitLength());
    }

    @Override
    public SMVType visit(EnumerateType enumerateType) {
        return new SMVType.EnumType(enumerateType.getAllowedValues());
    }

    @Override
    public SMVType visit(TimeType timeType) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(RecordType.Field field) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(RangeType rangeType) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(RecordType recordType) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(PointerType pointerType) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(IECString.String string) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(IECString.WString wString) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(IECArray iecArray) {
        throw new IllegalTypeException("Could not match");
    }

    @Override
    public SMVType visit(AnyNum anyNum) {
        throw new IllegalTypeException("Could not match");
    }
}