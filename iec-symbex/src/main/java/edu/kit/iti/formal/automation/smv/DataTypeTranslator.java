package edu.kit.iti.formal.automation.smv;

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.IllegalTypeException;
import edu.kit.iti.formal.smv.ast.GroundDataType;
import edu.kit.iti.formal.smv.ast.SMVType;

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
    public SMVType visit(AnyReal real) {
        return null;
    }

    @Override
    public SMVType visit(AnyReal.Real real) {
        return null;
    }

    @Override
    public SMVType visit(AnyReal.LReal real) {
        return null;
    }

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

    @Override public SMVType visit(ClassDataType classDataType) {
        return null;
    }
}
